module Absint2 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Inductive
open import Data.Nat.Order.Minmax
open import Data.String
open import Data.Maybe renaming (rec to recᵐ ; elim to elimᵐ)
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects
open import Data.Sum

open import Lang
open import State
open import AbsintCore

module AInt2
  (A : 𝒰)
  (top : A)
  (add : A → A → A)
  (fromN : ℕ → A)
  (to-pred : A → AExpr → Assert)
  (learn-from-success : St A → BExpr → Maybe (St A))
  (learn-from-failure : St A → BExpr → Maybe (St A))
  (join : A → A → A)
  (thinner : A → A → Bool)
  (over-approx : ℕ → St A → St A → St A)
  (choose-1 : St A → Instr → ℕ)
  (choose-2 : St A → Instr → ℕ)

  where

  open State.State A top
  open AbsintCore.AIntCore A top fromN add to-pred

  join-state : State → State → State
  join-state []             s2 = []
  join-state ((x , v) ∷ s1) s2 = stupd x (join v (stlup s2 x)) (join-state s1 s2)

  join-state-m : State → Maybe State → State
  join-state-m s1 (just s2) = join-state s1 s2
  join-state-m s1  nothing  = s1

  step1 : (State → AnInstr × Maybe State)
        → BExpr → State → State → State
  step1 ab b init s = recᵐ s (λ s′ → join-state-m init (ab s′ .snd)) (learn-from-success s b)

  step2 : (State → AnInstr × Maybe State)
        → BExpr → State → State → ℕ → State
  step2 ab b init s  zero   = s
  step2 ab b init s (suc n) = step2 ab b init (step1 ab b init s) n

  s-stable : State → State → Bool
  s-stable []             s2 = true
  s-stable ((x , v) ∷ s1) s2 = thinner (stlup s2 x) v and s-stable s1 s2

  is-inv : (State → AnInstr × Maybe State)
         → State → BExpr → Bool
  is-inv ab s b = s-stable s (step1 ab b s s)

  mutual
    find-inv : (State → AnInstr × Maybe State) → BExpr → State → State → Instr → ℕ → State
    find-inv ab b init s i n =
      let s' = step2 ab b init s (choose-1 s i) in
      if is-inv ab s' b then s' else find-inv-aux ab b init s s' i n

    find-inv-aux : (State → AnInstr × Maybe State) → BExpr → State → State → State → Instr → ℕ → State
    find-inv-aux ab b init s s' i  zero   = []
    find-inv-aux ab b init s s' i (suc n) =
      find-inv ab b init (over-approx n s s') i n

  {- mark dead code -}
  mark : Instr → AnInstr
  mark (Assign x e) = AnPre QFalse (AnAssign x e)
  mark (Seq i₁ i₂)  = AnSeq (mark i₁) (mark i₂)
  mark (While b i)  = AnWhile b QFalse (mark i)

  do-annot : (State → AnInstr × Maybe State)
           → BExpr → State → Instr → AnInstr
  do-annot ab b s i = recᵐ (mark i) (λ s′ → ab s′ .fst) (learn-from-success s b)

  ab2 : Instr → State → AnInstr × Maybe State
  ab2 (Assign x e) s = AnPre (s→a s) (AnAssign x e) , just (stupd x (a-af s e) s)
  ab2 (Seq i₁ i₂)  s = let (a_i1 , s1) = ab2 i₁ s in
                       recᵐ (AnSeq a_i1 (mark i₂) , nothing)
                            (λ s1′ → let (a_i2 , s2) = ab2 i₂ s1′ in
                                     AnSeq a_i1 a_i2 , s2)
                            s1
  ab2 (While b i)  s = let inv = find-inv (ab2 i) b s s i (choose-2 s i) in
                       (AnWhile b (s→a inv) (do-annot (ab2 i) b inv i)) , (learn-from-failure inv b)

module AInt2Sem
  (A : 𝒰)
  (top : A)
  (add : A → A → A)
  (fromN : ℕ → A)
  (to-pred : A → AExpr → Assert)
  (learn-from-success : St A → BExpr → Maybe (St A))
  (learn-from-failure : St A → BExpr → Maybe (St A))
  (join : A → A → A)
  (thinner : A → A → Bool)
  (over-approx : ℕ → St A → St A → St A)
  (choose-1 : St A → Instr → ℕ)
  (choose-2 : St A → Instr → ℕ)

  (m : String → List ℕ → 𝒰)

  (top-sem : ∀ {e} → to-pred top e ＝ QTrue)
  (subst-to-pred : ∀ {v x e e'} → qsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  (fromN-sem : ∀ {g x} → ia m g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ {g v e} → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (a-add-sem : ∀ {g v1 v2 x1 x2}
            → ia m g (to-pred v1 (ANum x1))
            → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))

  (join-thinner-1 : ∀ {a b} → is-true (thinner a (join a b)))
  (join-thinner-2 : ∀ {a b} → is-true (thinner b (join a b)))
  (thinner-sem : ∀ {a1 a2} → is-true (thinner a1 a2)
               → ∀ {g e} → ia m g (to-pred a1 e) → ia m g (to-pred a2 e))
  (let open State.State A top)
  (over-approx-consistent : ∀ {n s s'}
                          → consistent s → consistent s'
                          → consistent (over-approx n s s'))
  (learn-from-success-consistent : ∀ {s b s'}
                                 → consistent s
                                 → learn-from-success s b ＝ just s'
                                 → consistent s')
  (learn-from-failure-consistent : ∀ {s b s'}
                                 → consistent s
                                 → learn-from-failure s b ＝ just s'
                                 → consistent s')
  (let open AbsintCore.AIntCore A top fromN add to-pred)
  (over-approx-sem : ∀ {g n s s'}
                   → ia m g (s→a s)
                   → ia m g (s→a (over-approx n s s')))
  (learn-from-success-sem : ∀ {s b g}
                          → consistent s
                          → ia m g (s→a s) → ia m g (QB b)
                          → ia m g (s→a' (learn-from-success s b)))
  (learn-from-failure-sem : ∀ {s b g}
                          → consistent s
                          → ia m g (s→a s) → ¬ ia m g (QB b)
                          → ia m g (s→a' (learn-from-failure s b)))
  where

  open AIntCoreSem A top fromN add to-pred m top-sem fromN-sem to-pred-sem a-add-sem subst-to-pred
  open AInt2 A top add fromN to-pred learn-from-success learn-from-failure join thinner over-approx choose-1 choose-2

  join-safe-1 : ∀ {g a b x} → ia m g (to-pred a x) → ia m g (to-pred (join a b) x)
  join-safe-1 = thinner-sem join-thinner-1

  join-safe-2 : ∀ {g a b x} → ia m g (to-pred b x) → ia m g (to-pred (join a b) x)
  join-safe-2 = thinner-sem join-thinner-2

  upd-x : ∀ {g x e} s → ia m g (s→a (stupd x e s)) → ia m g (to-pred e (AVar x))
  upd-x             []            (iax , tt) = iax
  upd-x {g} {x} {e} ((y , v) ∷ s)            =
    elimᵈ {C = λ q → ia m g (s→a (if ⌊ q ⌋ then (y , e) ∷ s else (y , v) ∷ stupd x e s)) → ia m g (to-pred e (AVar x))}
          (λ p iax → subst (λ q → ia m g (to-pred e (AVar q))) (p ⁻¹) (iax .fst))
          (λ _ iax → upd-x s (iax .snd))
          (x ≟ y)

  upd-others : ∀ {g x e} s → ia m g (s→a (stupd x e s))
             → ∀ {y} → x ≠ y → ia m g (to-pred (stlup s y) (AVar y))
  upd-others {g}     {e} []            (iax , tt) {y} ne =
    subst (ia m g) (top-sem ⁻¹) tt
  upd-others {g} {x} {e} ((z , v) ∷ s)                   =
    elimᵈ {C = λ q → ia m g (s→a (if ⌊ q ⌋ then (z , e) ∷ s else (z , v) ∷ stupd x e s))
                   → {y : String} → x ≠ y
                   → ia m g (to-pred (if ⌊ y ≟ z ⌋ then v else stlup s y) (AVar y))}
          (λ p  iax {y} ne → elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))}
                                   (λ eq → absurd (ne (p ∙ eq ⁻¹)))
                                   (λ _  → transport (to-pred-sem ⁻¹) (lookup-sem s (iax .snd)))
                                   (y ≟ z) )
          (λ ¬p iax {y} ne → elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))}
                                   (λ eq → subst (λ q → ia m g (to-pred v (AVar q))) (eq ⁻¹) (iax .fst))
                                   (λ _  → upd-others s (iax .snd) ne)
                                   (y ≟ z) )
          (x ≟ z)

  join-state-consistent : ∀ {s2} s1 → consistent (join-state s1 s2)
  join-state-consistent      []             = tt
  join-state-consistent {s2} ((x , v) ∷ s1) = consistent-update {s = join-state s1 s2} (join-state-consistent s1)

  join-state-safe-1 : ∀ {g s2} s1 → ia m g (s→a s1) → ia m g (s→a (join-state s1 s2))
  join-state-safe-1          []             tt          = tt
  join-state-safe-1 {g} {s2} ((x , v) ∷ s1) (iax , ias) =
    a-upd-ia-all' {s = join-state s1 s2}
      (join-state-consistent s1)
      (λ {y} ne → transport (to-pred-sem ⁻¹)
                            (lookup-sem (join-state s1 s2) (join-state-safe-1 s1 ias)))
      (join-safe-1 iax)

  join-state-safe-2 : ∀ {g s2} s1 → ia m g (s→a s2) → ia m g (s→a (join-state s1 s2))
  join-state-safe-2          []             iax = tt
  join-state-safe-2 {g} {s2} ((x , v) ∷ s1) iax =
    a-upd-ia-all' {s = join-state s1 s2}
      (join-state-consistent s1)
      (λ {y} ne → transport (to-pred-sem ⁻¹)
                            (lookup-sem (join-state s1 s2) (join-state-safe-2 s1 iax)))
      (join-safe-2 (transport (to-pred-sem ⁻¹)
                              (lookup-sem s2 iax)))

  step1-pc : ∀ {g ab b s s'}
           → ia m g (s→a s) → ia m g (s→a s')
           → ia m g (s→a (step1 ab b s s'))
  step1-pc {g} {ab} {b} {s} {s'} ias ias' =
    elimᵐ (λ q → ia m g (s→a (recᵐ s' (λ s′ → join-state-m s (ab s′ .snd)) q)))
          ias'
          (λ x → elimᵐ (λ q → ia m g (s→a (join-state-m s q)))
                       ias
                       (λ y → join-state-safe-1 s ias)
                       (ab x .snd))
          (learn-from-success s' b)

  step2-pc : ∀ {g ab b s s'} n
           → ia m g (s→a s) → ia m g (s→a s')
           → ia m g (s→a (step2 ab b s s' n))
  step2-pc       zero   ias ias' = ias'
  step2-pc {ab} (suc n) ias ias' = step2-pc n ias (step1-pc {ab = ab} ias ias')

  mutual
    find-inv-pc : ∀ {g ab init s b i} n
                → ia m g (s→a s) → ia m g (s→a init)
                → ia m g (s→a (find-inv ab b init s i n))
    find-inv-pc {ab} {init} {s} {b} {i} n ias iai with is-inv ab (step2 ab b init s (choose-1 s i)) b
    ... | false = find-inv-aux-pc n ias iai
    ... | true  = step2-pc (choose-1 s i) iai ias

    find-inv-aux-pc : ∀ {g ab init s s' b i} n
                → ia m g (s→a s) → ia m g (s→a init)
                → ia m g (s→a (find-inv-aux ab b init s s' i n))
    find-inv-aux-pc  zero   ias iai = tt
    find-inv-aux-pc (suc n) ias iai =
      find-inv-pc n (over-approx-sem ias) iai

  ab2-pc : ∀ {i' s s'} i
         → ab2 i s ＝ (i' , s')
         → ∀ {g a} → ia m g (s→a s)
         → ia m g (pc i' a)
  ab2-pc               (Assign x e) q {g} {a} is =
    subst (λ q → ia m g (pc q a)) (ap fst q) is
  ab2-pc {i'} {s} {s'} (Seq i₁ i₂)               =
    elimᵐ (λ q → recᵐ (AnSeq (ab2 i₁ s .fst) (mark i₂) , nothing)
                      (λ s1′ → AnSeq (ab2 i₁ s .fst) (ab2 i₂ s1′ .fst) , ab2 i₂ s1′ .snd)
                      q ＝ (i' , s')
               → ∀ {g a} → ia m g (s→a s) → ia m g (pc i' a))
      (λ q {g} {a} is → subst (λ q → ia m g (pc q a)) (ap fst q)
                              (ab2-pc {i' = ab2 i₁ s .fst} i₁ refl is))
      (λ st q {g} {a} is → subst (λ q → ia m g (pc q a)) (ap fst q)
                                 (ab2-pc {i' = ab2 i₁ s .fst} i₁ refl is))
      (ab2 i₁ s .snd)
  ab2-pc      {s}      (While b i)  q {g} {a} is =
    subst (λ q → ia m g (pc q a)) (ap fst q)
      (find-inv-pc (choose-2 s i) is is)

  vc-mark : ∀ i → valid m (vc (mark i) QFalse)
  vc-mark (Assign x e) = (λ _ → id) , tt
  vc-mark (Seq i₁ i₂)  = valid-cat (vc (mark i₁) (pc (mark i₂) QFalse))
                                   (vc-monotonic strong (mark i₁) (vc-mark i₁) .fst)
                                   (vc-mark i₂)
    where
    strong : ∀ g → ia m g QFalse → ia m g (pc (mark i₂) QFalse)
    strong g c = absurd c
  vc-mark (While b i)  = (λ _ h → absurd (h .fst)) , (λ _ h → h .fst) , vc-mark i

  step1-consistent : ∀ {ab b s s'}
                   → (∀ s s′ i → consistent s → ab s ＝ (i , just s′) → consistent s′)
                   → consistent s → consistent s'
                   → consistent (step1 ab b s s')
  step1-consistent {ab} {b} {s} {s'} cab cs cs' =
    elimᵐ (λ q → consistent (recᵐ s' (λ s′ → join-state-m s (ab s′ .snd)) q))
          cs'
          (λ x → elimᵐ (λ q → consistent (join-state-m s q))
                       cs
                       (λ y → join-state-consistent s)
                       (ab x .snd))
          (learn-from-success s' b)

  step2-consistent : ∀ {ab b s s'} n
                   → (∀ s s′ i → consistent s → ab s ＝ (i , just s′) → consistent s′)
                   → consistent s → consistent s'
                   → consistent (step2 ab b s s' n)
  step2-consistent  zero   cab cs cs' = cs'
  step2-consistent (suc n) cab cs cs' = step2-consistent n cab cs (step1-consistent cab cs cs')

  mutual
    find-inv-consistent : ∀ {ab b init s i} n
                        → (∀ s s′ i → consistent s → ab s ＝ (i , just s′) → consistent s′)
                        → consistent s → consistent init
                        → consistent (find-inv ab b init s i n)
    find-inv-consistent {ab} {b} {init} {s} {i} n cab cs ci with is-inv ab (step2 ab b init s (choose-1 s i)) b
    ... | false = find-inv-aux-consistent n cab cs ci (step2-consistent (choose-1 s i) cab ci cs)
    ... | true  = step2-consistent (choose-1 s i) cab ci cs

    find-inv-aux-consistent : ∀ {ab init s s' b i} n
                            → (∀ s s′ i → consistent s → ab s ＝ (i , just s′) → consistent s′)
                            → consistent s → consistent init → consistent s'
                            → consistent (find-inv-aux ab b init s s' i n)
    find-inv-aux-consistent  zero   cab cs ci cs' = tt
    find-inv-aux-consistent (suc n) cab cs ci cs' =
      find-inv-consistent n cab (over-approx-consistent cs cs') ci

  ab2-consistent : ∀ {s s' i'} i
                 → consistent s
                 → ab2 i s ＝ (i' , just s')
                 → consistent s'
  ab2-consistent {s}           (Assign x e) cs q =
    subst consistent (just-inj (ap snd q)) (consistent-update {s = s} cs)
  ab2-consistent {s} {s'} {i'} (Seq i₁ i₂)  cs   =
    elimᵐ (λ q → ab2 i₁ s .snd ＝ q
               → recᵐ (AnSeq (ab2 i₁ s .fst) (mark i₂) , nothing)
                      (λ s1′ → AnSeq (ab2 i₁ s .fst) (ab2 i₂ s1′ .fst) , ab2 i₂ s1′ .snd)
                      q
                 ＝ (i' , just s') → consistent s')
      (λ _ q   → absurd (nothing≠just (ap snd q)))
      (λ st e1 → elimᵐ (λ q → ab2 i₂ st .snd ＝ q
                            →  (AnSeq (ab2 i₁ s .fst) (ab2 i₂ st .fst) , q) ＝
                              (i' , just s')
                            → consistent s')
                       (λ _ q → absurd (nothing≠just (ap snd q)))
                       (λ st' e2 q → ab2-consistent i₂
                                    (ab2-consistent i₁ cs (×-path refl e1))
                                    (×-path refl (e2 ∙ ap snd q))
                        )
                       (ab2 i₂ st .snd) refl)
      (ab2 i₁ s .snd) refl
  ab2-consistent {s} {s'} {i'} (While b i)  cs    =
    elimᵐ (λ q → learn-from-failure (find-inv (ab2 i) b s s i (choose-2 s i)) b ＝ q
               → ( AnWhile b (s→a (find-inv (ab2 i) b s s i (choose-2 s i)))
                             (do-annot (ab2 i) b (find-inv (ab2 i) b s s i (choose-2 s i)) i)
                 , q ) ＝ (i' , just s')
               → consistent s')
      (λ _ q    → absurd (nothing≠just (ap snd q)))
      (λ st e q → learn-from-failure-consistent
                    (find-inv-consistent (choose-2 s i)
                                         (λ s₁ s′ i₁ → ab2-consistent i)
                                         cs cs)
                    (e ∙ ap snd q))
      (learn-from-failure (find-inv (ab2 i) b s s i (choose-2 s i)) b) refl

  mark-pc : ∀ i → pc (mark i) QFalse ＝ QFalse
  mark-pc (Assign x e) = refl
  mark-pc (Seq i₁ i₂)  = subst (λ q → pc (mark i₁) q ＝ QFalse) ((mark-pc i₂) ⁻¹) (mark-pc i₁)
  mark-pc (While b i)  = refl

  do-annot-pc : ∀ {b g i a s}
              → ia m g (s→a' (learn-from-success s b))
              → ia m g (pc (do-annot (ab2 i) b s i) a)
  do-annot-pc {b} {g} {i} {a} {s} =
    elimᵐ (λ q → ia m g (s→a' q) → ia m g (pc (recᵐ (mark i) (λ s′ → ab2 i s′ .fst) q) a))
          (λ c  → absurd c)
          (λ st → ab2-pc i refl)
          (learn-from-success s b)

  s-stable-correct : ∀ {g s'} s
                   → is-true (s-stable s s')
                   → ia m g (s→a s')
                   → ia m g (s→a s)
  s-stable-correct          []            ss ias' = tt
  s-stable-correct {g} {s'} ((x , v) ∷ s) ss ias' =
    let hh = and-true-≃ {x = thinner (stlup s' x) v} {y = s-stable s s'} $ is-true≃is-trueₚ $ ss in
      thinner-sem (is-true≃is-trueₚ ⁻¹ $ hh .fst)
         (transport (to-pred-sem ⁻¹) (lookup-sem s' ias'))
    , s-stable-correct s (is-true≃is-trueₚ ⁻¹ $  hh .snd) ias'

  is-inv-correct : ∀ {ab b g s s' ai} s2
                 → is-true (is-inv ab s b)
                 → learn-from-success s b ＝ just s'
                 → ab s' ＝ (ai , s2)
                 → ia m g (s→a' s2)
                 → ia m g (s→a s)
  is-inv-correct {ab} {s} (just x) st ql qab ias2 =
    let st' = subst (λ q → is-true (s-stable s (join-state-m s (q .snd)))) qab $
              subst (λ q → is-true (s-stable s (recᵐ s (λ s′ → join-state-m s (ab s′ .snd)) q))) ql
              st in
    s-stable-correct s st' (join-state-safe-2 s ias2)
  is-inv-correct          nothing  st ql qab ias2 = absurd ias2

  mutual
    find-inv-correct : ∀ {ab b g i init s s' s2 ai} n
                     → learn-from-success (find-inv ab b init s i n) b ＝ just s'
                     → ab s' ＝ (ai , s2)
                     → ia m g (s→a' s2)
                     → ia m g (s→a (find-inv ab b init s i n))
    find-inv-correct {ab} {b} {g} {i} {init} {s} {s'} {s2} n ql qab ias2 with is-inv ab (step2 ab b init s (choose-1 s i)) b | recall (is-inv ab (step2 ab b init s (choose-1 s i))) b
    ... | false | ⟪ _ ⟫  = find-inv-aux-correct n ql qab ias2
    ... | true  | ⟪ eq ⟫ = is-inv-correct {ab = ab} s2 (is-true≃is-trueₚ ⁻¹ $ eq) ql qab ias2

    find-inv-aux-correct : ∀ {ab b g i init s s′ s″ s2 ai} n
                         → learn-from-success (find-inv-aux ab b init s s′ i n) b ＝ just s″
                         → ab s″ ＝ (ai , s2)
                         → ia m g (s→a' s2)
                         → ia m g (s→a (find-inv-aux ab b init s s′ i n))
    find-inv-aux-correct  zero   ql qab ias2 = tt
    find-inv-aux-correct (suc n) ql qab ias2 = find-inv-correct n ql qab ias2

  ab2-correct : ∀ {i' s s'} i
              → consistent s
              → ab2 i s ＝ (i' , s')
              → valid m (vc i' (s→a' s'))
  ab2-correct {i'} {s}      (Assign x e) cs eq =
    subst (λ q → valid m (vc i' (s→a' q))) (ap snd eq) $
    subst (λ q → valid m (vc q (s→a (stupd x (a-af s e) s)))) (ap fst eq) $
    (λ g ias → subst-consistent {s = s} cs ias (a-af-sound e ias)) , tt
  ab2-correct {i'} {s} {s'} (Seq i₁ i₂)  cs    =
    elimᵐ (λ q → ab2 i₁ s .snd ＝ q
               → recᵐ (AnSeq (ab2 i₁ s .fst) (mark i₂) , nothing)
                      (λ s1′ → AnSeq (ab2 i₁ s .fst) (ab2 i₂ s1′ .fst) , ab2 i₂ s1′ .snd)
                      q
                 ＝ (i' , s')
               → valid m (vc i' (s→a' s')))
          (λ e eq    → subst (λ q → valid m (vc i' (s→a' q))) (ap snd eq) $
                      subst (λ q → valid m (vc q QFalse)) (ap fst eq) $
                      valid-cat (vc (ab2 i₁ s .fst) (pc (mark i₂) QFalse))
                                (subst (λ q → valid m (vc (ab2 i₁ s .fst) q)) (mark-pc i₂ ⁻¹)
                                       (ab2-correct i₁ cs (×-path refl e)))
                                (vc-mark i₂))
          (λ st e eq → subst (λ q → valid m (vc i' (s→a' q))) (ap snd eq) $
                      subst (λ q → valid m (vc q (s→a' (ab2 i₂ st .snd)))) (ap fst eq) $
                      valid-cat (vc (ab2 i₁ s .fst) (pc (ab2 i₂ st .fst) (s→a' (ab2 i₂ st .snd))))
                                (vc-monotonic (λ g ias1 → ab2-pc i₂ refl ias1)
                                              (ab2 i₁ s .fst)
                                              (ab2-correct i₁ cs (×-path refl e))
                                              .fst)
                                (ab2-correct i₂ (ab2-consistent i₁ cs (×-path refl e)) refl))
          (ab2 i₁ s .snd) refl
  ab2-correct {i'} {s} {s'} (While b i)  cs eq =
    subst (λ q → valid m (vc i' (s→a' q))) (ap snd eq) $
    let inv = find-inv (ab2 i) b s s i (choose-2 s i) in
    subst (λ q → valid m (vc q (s→a' (learn-from-failure inv b)))) (ap fst eq) $
      (λ g iafgb → do-annot-pc $
                   learn-from-success-sem
                      (find-inv-consistent (choose-2 s i) (λ s₁ s′ i₁ → ab2-consistent i) cs cs)
                      (iafgb .fst)
                      (iafgb .snd))
    , (λ g iafngb → learn-from-failure-sem
                      (find-inv-consistent (choose-2 s i) (λ s₁ s′ i₁ → ab2-consistent i) cs cs)
                      (iafngb .fst)
                      (iafngb .snd))
    , elimᵐ (λ q → learn-from-success inv b ＝ q
                 → valid m (vc (recᵐ (mark i) (λ s′ → ab2 i s′ .fst) q) (s→a inv)))
            (λ _ → vc-monotonic (λ _ c → absurd c) (mark i) (vc-mark i) .fst)
            (λ st e → vc-monotonic {p1 = s→a' (ab2 i st .snd)}
                        (λ g → find-inv-correct (choose-2 s i) e refl)
                        (ab2 i st .fst)
                        (ab2-correct i
                           (learn-from-success-consistent
                              (find-inv-consistent (choose-2 s i)
                                 (λ s₁ s′ i₁ → ab2-consistent i) cs cs)
                              e) refl)
                      .fst)
            (learn-from-success inv b) refl

  mark-clean : ∀ i → cleanup (mark i) ＝ i
  mark-clean (Assign x e) = refl
  mark-clean (Seq i₁ i₂)  = ap² Seq (mark-clean i₁) (mark-clean i₂)
  mark-clean (While b i)  = ap (While b) (mark-clean i)

  ab2-clean : ∀ {i' s s'} i
            → ab2 i s ＝ (i' , s')
            → cleanup i' ＝ i
  ab2-clean               (Assign x e) eq =
    subst (λ q → cleanup q ＝ Assign x e) (ap fst eq) refl
  ab2-clean {i'} {s} {s'} (Seq i₁ i₂)     =
    elimᵐ (λ q → recᵐ (AnSeq (ab2 i₁ s .fst) (mark i₂) , nothing)
                      (λ s1′ → AnSeq (ab2 i₁ s .fst) (ab2 i₂ s1′ .fst) , ab2 i₂ s1′ .snd)
                      q
                 ＝ (i' , s')
               → cleanup i' ＝ Seq i₁ i₂ )
          (λ eq → subst (λ q → cleanup q ＝ Seq i₁ i₂) (ap fst eq) $
                  ap² Seq (ab2-clean i₁ refl) (mark-clean i₂))
          (λ st eq → subst (λ q → cleanup q ＝ Seq i₁ i₂) (ap fst eq) $
                     ap² Seq (ab2-clean i₁ refl) (ab2-clean i₂ refl))
          (ab2 i₁ s .snd)
  ab2-clean      {s}      (While b i)  eq =
    subst (λ q → cleanup q ＝ While b i) (ap fst eq) $
    ap (While b) $
    elimᵐ (λ q → cleanup (recᵐ (mark i) (λ s′ → ab2 i s′ .fst) q) ＝ i)
          (mark-clean i)
          (λ st → ab2-clean i refl)
          (learn-from-success (find-inv (ab2 i) b s s i (choose-2 s i)) b)

-- testing

data Interval : 𝒰 where
  Above   : ℕ → Interval
  Below   : ℕ → Interval
  Between : ℕ → ℕ → Interval
  AllN    : Interval

i-fromN : ℕ → Interval
i-fromN x = Between x x

i-add : Interval → Interval → Interval
i-add (Above x)     (Above y)     = Above (x + y)
i-add (Above x)     (Between y _) = Above (x + y)
i-add (Below x)     (Below y)     = Below (x + y)
i-add (Below x)     (Between _ z) = Below (x + z)
i-add (Between x _) (Above z)     = Above (x + z)
i-add (Between _ y) (Below z)     = Below (y + z)
i-add (Between x y) (Between z w) = Between (x + z) (y + w)
i-add _             _             = AllN

i-to-pred : Interval → AExpr → Assert
i-to-pred (Above x)     e = QPred "leq" (ANum x ∷ e ∷ [])
i-to-pred (Below x)     e = QPred "leq" (e ∷ ANum x ∷ [])
i-to-pred (Between x y) e = QConj (QPred "leq" (ANum x ∷ e ∷ []))
                                  (QPred "leq" (e ∷ ANum y ∷ []))
i-to-pred  AllN         _ = QTrue

open module IState = State.State Interval AllN
open module IInt = AIntCore Interval AllN i-fromN i-add i-to-pred

-- TODO upstream

i-learn-from-success-aux : State → String → Interval → Interval → Maybe State
i-learn-from-success-aux s n (Below x)     (Above y)     = if x ≤ᵇ y then nothing
                                                                     else just (stupd n (Between y (pred x)) s)
i-learn-from-success-aux s n (Below x)     (Below y)     = just (if x ≤ᵇ y then stupd n (Below (pred x)) s
                                                                           else s)
i-learn-from-success-aux s n (Below x)     (Between y z) = if x ≤ᵇ y then nothing
                                                                     else just (stupd n (Between y (min (pred x) z)) s)
i-learn-from-success-aux s n (Below x)      AllN         = just (stupd n (Below (pred x)) s)
i-learn-from-success-aux s n (Between _ y) (Above z)     = if y ≤ᵇ z then nothing
                                                                     else just (stupd n (Between z (pred y)) s)
i-learn-from-success-aux s n (Between _ y) (Below z)     = just (if y ≤ᵇ z then stupd n (Below (pred y)) s
                                                                           else s)
i-learn-from-success-aux s n (Between _ y) (Between z w) = if y ≤ᵇ z then nothing
                                                                     else just (if y ≤ᵇ w then stupd n (Between z (pred y)) s
                                                                                          else s)
i-learn-from-success-aux s n (Between _ y)  AllN         = just (stupd n (Below (pred y)) s)
i-learn-from-success-aux s _ _              _            = just s

i-learn-from-success : State → BExpr → Maybe State
i-learn-from-success s (BLt (AVar n) e) = i-learn-from-success-aux s n (a-af s e) (stlup s n)
i-learn-from-success s _                = just s

i-learn-from-failure-aux : State → String → Interval → Interval → Maybe State
i-learn-from-failure-aux s n (Above x)     (Above y)     = just (if x ≤ᵇ y then s
                                                                           else stupd n (Above x) s)
i-learn-from-failure-aux s n (Above x)     (Below y)     = if x ≤ᵇ y then just (stupd n (Between x y) s)
                                                                     else nothing
i-learn-from-failure-aux s n (Above x)     (Between y z) = if z <ᵇ x then nothing
                                                                     else just (if x ≤ᵇ y then s else stupd n (Between x z) s)
i-learn-from-failure-aux s n (Above x)      AllN         = just (stupd n (Above x) s)
i-learn-from-failure-aux s n (Between x _) (Above z)     = just (if x ≤ᵇ z then s
                                                                           else stupd n (Above x) s)
i-learn-from-failure-aux s n (Between x _) (Below z)     = if x ≤ᵇ z then just (stupd n (Between x z) s)
                                                                     else nothing
i-learn-from-failure-aux s n (Between x _) (Between z w) = if w <ᵇ x then nothing
                                                                     else just (if x ≤ᵇ z then s
                                                                                          else stupd n (Between x w) s)
i-learn-from-failure-aux s n (Between x _)  AllN         = just (stupd n (Above x) s)
i-learn-from-failure-aux s _ _              _            = just s

i-learn-from-failure : State → BExpr → Maybe State
i-learn-from-failure s (BLt (AVar n) e) = i-learn-from-failure-aux s n (a-af s e) (stlup s n)
i-learn-from-failure s _                = just s

i-join : Interval → Interval → Interval
i-join (Above x)     (Above y)     = Above (min x y)
i-join (Above x)     (Between y _) = Above (min x y)
i-join (Below x)     (Below y)     = Below (max x y)
i-join (Below x)     (Between _ z) = Below (max x z)
i-join (Between x _) (Above z)     = Above (min x z)
i-join (Between _ y) (Below z)     = Below (max y z)
i-join (Between x y) (Between z w) = Between (min x z) (max y w)
i-join _             _             = AllN

i-thinner : Interval → Interval → Bool
i-thinner (Above x)     (Above y)     = y ≤ᵇ x
i-thinner (Below x)     (Below y)     = x ≤ᵇ y
i-thinner (Between x _) (Above z)     = z ≤ᵇ x
i-thinner (Between _ y) (Below z)     = y ≤ᵇ z
i-thinner (Between x y) (Between z w) = (z ≤ᵇ x) and (y ≤ᵇ w)
i-thinner _              AllN         = true
i-thinner _              _            = false

open-interval : Interval → Interval → Interval
open-interval i@(Above x)     (Above y)     = if x ≤ᵇ y then i else AllN
open-interval i@(Below x)     (Below y)     = if y ≤ᵇ x then i else AllN
open-interval i@(Between x y) (Between z w) = if x ≤ᵇ z
                                                  then if w ≤ᵇ y then i else Above x
                                                  else if w ≤ᵇ y then Below y else AllN
open-interval    _              _            = AllN

open-intervals : State → State → State
open-intervals s s' = map (λ p → let (n , v) = p in n , open-interval v (stlup s' n)) s

i-over-approx : ℕ → State → State → State
i-over-approx  zero   s s' = []
i-over-approx (suc _) s s' = open-intervals s s'

-- TODO prop

i-choose-1 : State → Instr → ℕ
i-choose-1 _ _ = 2

i-choose-2 : State → Instr → ℕ
i-choose-2 _ _ = 3

open module IntervalInt = AInt2 Interval AllN i-add i-fromN i-to-pred
                                i-learn-from-success i-learn-from-failure
                                i-join i-thinner i-over-approx
                                i-choose-1 i-choose-2

-- the program in the intro
i-1 : Instr
i-1 = While (BLt (AVar "x") (ANum 10))
            (Assign "x" (APlus (AVar "x") (ANum 1)))

s-1 : State
s-1 = ("x" , i-fromN 0) ∷ []

res-1-1 : AnInstr
res-1-1 = AnWhile (BLt (AVar "x") (ANum 10))
                    (QConj
                      (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                             (QPred "leq" (AVar "x" ∷ ANum 10 ∷ [])))
                      QTrue)
                  (AnPre (QConj
                           (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                  (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                           QTrue)
                         (AnAssign "x" (APlus (AVar "x") (ANum 1))))

res-1 : AnInstr × Maybe State
res-1 = res-1-1 , just (("x" , Between 10 10) ∷ [])

test-1 : ab2 i-1 s-1 ＝ res-1
test-1 = refl

i-2 : Instr
i-2 = Seq (Assign "x" (ANum 0)) i-1

res-2 : AnInstr × Maybe State
res-2 = AnSeq (AnPre QTrue (AnAssign "x" (ANum 0))) res-1-1
      , just (("x" , Between 10 10) ∷ [])

test-2 : ab2 i-2 [] ＝ res-2
test-2 = refl

i-3 : Instr
i-3 = While (BLt (AVar "x") (ANum 10))
            (Seq (While (BLt (AVar "y") (AVar "x"))
                        (Assign "y" (APlus (AVar "y") (ANum 1))))
            (Seq (Assign "y" (ANum 0))
                 (Assign "x" (APlus (AVar "x") (ANum 1)))))

s-3 : State
s-3 = ("x" , i-fromN 0) ∷ ("y" , i-fromN 0) ∷ []

res-3 : AnInstr × Maybe State
res-3 =   AnWhile (BLt (AVar "x") (ANum 10))
                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                (QPred "leq" (AVar "y" ∷ ANum 0 ∷ [])))
                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                (QPred "leq" (AVar "x" ∷ ANum 10 ∷ [])))
                   QTrue))
                  (AnSeq (AnWhile (BLt (AVar "y") (AVar "x"))
                                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                                (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                                (QPred "leq" (AVar "y" ∷ ANum 9 ∷ [])))
                                   QTrue))
                                  (AnPre (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                                       (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                         (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                                       (QPred "leq" (AVar "y" ∷ ANum 8 ∷ [])))
                                          QTrue))
                                         (AnAssign "y" (APlus (AVar "y") (ANum 1)))))
                  (AnSeq (AnPre (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                              (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                              (QPred "leq" (AVar "y" ∷ ANum 9 ∷ [])))
                                 QTrue))
                                (AnAssign "y" (ANum 0)))
                         (AnPre (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                              (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                              (QPred "leq" (AVar "y" ∷ ANum 0 ∷ [])))
                                 QTrue))
                                (AnAssign "x" (APlus (AVar "x") (ANum 1))))))
        , just (("y" , Between 0 0) ∷ ("x" , Between 10 10) ∷ [])

test-3 : ab2 i-3 s-3 ＝ res-3
test-3 = refl

-- properties

i-m-aux : List ℕ → 𝒰
i-m-aux (x ∷ y ∷ []) = x ≤ y
i-m-aux _            = ⊥

i-m : String → List ℕ → 𝒰
i-m s l = if ⌊ s ≟ "leq" ⌋ then i-m-aux l else ⊥

i-top-sem : ∀ {e} → i-to-pred AllN e ＝ QTrue
i-top-sem = refl

i-to-pred-sem : ∀ {g v e} → ia i-m g (i-to-pred v e) ＝ ia i-m g (i-to-pred v (ANum (af g e)))
i-to-pred-sem {v = Above x}     = refl
i-to-pred-sem {v = Below x}     = refl
i-to-pred-sem {v = Between x y} = refl
i-to-pred-sem {v = AllN}        = refl

i-subst-to-pred : ∀ {v x e e'} → qsubst x e' (i-to-pred v e) ＝ i-to-pred v (asubst x e' e)
i-subst-to-pred {v = Above x}     = refl
i-subst-to-pred {v = Below x}     = refl
i-subst-to-pred {v = Between x y} = refl
i-subst-to-pred {v = AllN}        = refl

i-fromN-sem : ∀ {g x} → ia i-m g (i-to-pred (i-fromN x) (ANum x))
i-fromN-sem = ≤-refl , ≤-refl

i-add-sem : ∀ {g v1 v2 x1 x2}
          → ia i-m g (i-to-pred v1 (ANum x1))
          → ia i-m g (i-to-pred v2 (ANum x2))
          → ia i-m g (i-to-pred (i-add v1 v2) (ANum (x1 + x2)))
i-add-sem {v1 = Above x}     {v2 = Above y}     h1        h2        = ≤-cong-+ _ _ _ _ h1 h2
i-add-sem {v1 = Above _}     {v2 = Below _}     _         _         = tt
i-add-sem {v1 = Above x}     {v2 = Between y z} h1        (h2 , _)  = ≤-cong-+ _ _ _ _ h1 h2
i-add-sem {v1 = Above _}     {v2 = AllN}        _         _         = tt
i-add-sem {v1 = Below _}     {v2 = Above _}     _         _         = tt
i-add-sem {v1 = Below x}     {v2 = Below t}     h1        h2        = ≤-cong-+ _ _ _ _ h1 h2
i-add-sem {v1 = Below x}     {v2 = Between y z} h1        (_ , h2)  = ≤-cong-+ _ _ _ _ h1 h2
i-add-sem {v1 = Below x}     {v2 = AllN}        _         _         = tt
i-add-sem {v1 = Between x y} {v2 = Above z}     (h1 , _)  h2        = ≤-cong-+ _ _ _ _ h1 h2
i-add-sem {v1 = Between x y} {v2 = Below z}     (_  , h1) h2        = ≤-cong-+ _ _ _ _ h1 h2
i-add-sem {v1 = Between x y} {v2 = Between z w} (h1 , h2) (h3 , h4) = ≤-cong-+ _ _ _ _ h1 h3
                                                                    , ≤-cong-+ _ _ _ _ h2 h4
i-add-sem {v1 = Between x y} {v2 = AllN}        _         _         = tt
i-add-sem {v1 = AllN}                           _         _         = tt

open-interval-sem : ∀ {g s n} v
                    → ia i-m g (i-to-pred v (AVar n))
                    → ia i-m g (i-to-pred (open-interval v (stlup s n)) (AVar n))
open-interval-sem {s} {n} (Above x)     ian with stlup s n
open-interval-sem         (Above x)     ian | Above y     with x ≤ᵇ y
open-interval-sem         (Above x)     ian | Above y | true  = ian
open-interval-sem         (Above x)     ian | Above y | false = tt
open-interval-sem         (Above _)     ian | Below _     = tt
open-interval-sem         (Above _)     ian | Between _ _ = tt
open-interval-sem         (Above _)     ian | AllN        = tt
open-interval-sem {s} {n} (Below x)     ian with stlup s n
open-interval-sem         (Below _)     ian | Above _      = tt
open-interval-sem         (Below x)     ian | Below y     with y ≤ᵇ x
open-interval-sem         (Below x)     ian | Below y | true  = ian
open-interval-sem         (Below x)     ian | Below y | false = tt
open-interval-sem         (Below _)     ian | Between _ _ = tt
open-interval-sem         (Below _)     ian | AllN        = tt
open-interval-sem {s} {n} (Between x y) ian with stlup s n
open-interval-sem         (Between _ _) ian | Above _     = tt
open-interval-sem         (Between _ _) ian | Below _     = tt
open-interval-sem         (Between x y) ian | Between z w with x ≤ᵇ z
open-interval-sem         (Between x y) ian | Between z w | true  with w ≤ᵇ y
open-interval-sem         (Between x y) ian | Between z w | true | true  = ian
open-interval-sem         (Between x y) ian | Between z w | true | false = ian .fst
open-interval-sem         (Between x y) ian | Between z w | false with w ≤ᵇ y
open-interval-sem         (Between x y) ian | Between z w | false | true  = ian .snd
open-interval-sem         (Between x y) ian | Between z w | false | false = tt
open-interval-sem         (Between _ _) ian | AllN        = tt
open-interval-sem          AllN         ian = tt

open-intervals-sem : ∀ {g s'} s
                    → ia i-m g (s→a s)
                    → ia i-m g (s→a (open-intervals s s'))
open-intervals-sem      []            tt          = tt
open-intervals-sem {s'} ((x , v) ∷ s) (iax , ias) =
  open-interval-sem {s = s'} v iax , open-intervals-sem {s' = s'} s ias

i-over-approx-sem : ∀ {g n s s'}
                  → ia i-m g (s→a s)
                  → ia i-m g (s→a (i-over-approx n s s'))
i-over-approx-sem {n = zero}           ias = tt
i-over-approx-sem {n = suc n} {s} {s'} ias = open-intervals-sem {s' = s'} s ias

i-join-thinner-1 : ∀ {a b} → is-true (i-thinner a (i-join a b))
i-join-thinner-1 {a = Above x}     {b = Above y}     = min-l {x = x} {y = y}
i-join-thinner-1 {a = Above _}     {b = Below _}     = tt
i-join-thinner-1 {a = Above x}     {b = Between y z} = min-l {x = x} {y = y}
i-join-thinner-1 {a = Above _}     {b = AllN}        = tt
i-join-thinner-1 {a = Below _}     {b = Above _}     = tt
i-join-thinner-1 {a = Below x}     {b = Below y}     = max-l {x = x} {y = y}
i-join-thinner-1 {a = Below x}     {b = Between y z} = max-l {x = x} {y = z}
i-join-thinner-1 {a = Below _}     {b = AllN}        = tt
i-join-thinner-1 {a = Between x y} {b = Above z}     = min-l {x = x} {y = z}
i-join-thinner-1 {a = Between x y} {b = Below z}     = max-l {x = y} {y = z}
i-join-thinner-1 {a = Between x y} {b = Between z w} =
  is-true≃is-trueₚ ⁻¹ $ and-true-≃ {x = min x z ≤ᵇ x} {y = y ≤ᵇ max y w} ⁻¹ $
  (is-true≃is-trueₚ $ min-l {x = x} {y = z}) , (is-true≃is-trueₚ $ max-l {x = y} {y = w})
i-join-thinner-1 {a = Between _ _} {b = AllN}        = tt
i-join-thinner-1 {a = AllN}        {b = Above _}     = tt
i-join-thinner-1 {a = AllN}        {b = Below _}     = tt
i-join-thinner-1 {a = AllN}        {b = Between _ _} = tt
i-join-thinner-1 {a = AllN}        {b = AllN}        = tt

i-join-thinner-2 : ∀ {a b} → is-true (i-thinner b (i-join a b))
i-join-thinner-2 {a = Above x}     {b = Above y}     = min-r {x = x} {y = y}
i-join-thinner-2 {a = Above _}     {b = Below _}     = tt
i-join-thinner-2 {a = Above x}     {b = Between y z} = min-r {x = x} {y = y}
i-join-thinner-2 {a = Above _}     {b = AllN}        = tt
i-join-thinner-2 {a = Below _}     {b = Above _}     = tt
i-join-thinner-2 {a = Below x}     {b = Below y}     = max-r {x = x} {y = y}
i-join-thinner-2 {a = Below x}     {b = Between y z} = max-r {x = x} {y = z}
i-join-thinner-2 {a = Below _}     {b = AllN}        = tt
i-join-thinner-2 {a = Between x y} {b = Above z}     = min-r {x = x} {y = z}
i-join-thinner-2 {a = Between x y} {b = Below z}     = max-r {x = y} {y = z}
i-join-thinner-2 {a = Between x y} {b = Between z w} =
  is-true≃is-trueₚ ⁻¹ $ and-true-≃ {x = min x z ≤ᵇ z} {y = w ≤ᵇ max y w} ⁻¹ $
  (is-true≃is-trueₚ $ min-r {x = x} {y = z}) , (is-true≃is-trueₚ $ max-r {x = y} {y = w})
i-join-thinner-2 {a = Between _ _} {b = AllN}        = tt
i-join-thinner-2 {a = AllN}        {b = Above _}     = tt
i-join-thinner-2 {a = AllN}        {b = Below _}     = tt
i-join-thinner-2 {a = AllN}        {b = Between _ _} = tt
i-join-thinner-2 {a = AllN}        {b = AllN}        = tt

i-thinner-sem : ∀ {a1 a2} → is-true (i-thinner a1 a2)
              → ∀ {g e} → ia i-m g (i-to-pred a1 e)
              → ia i-m g (i-to-pred a2 e)
i-thinner-sem {a1 = Above x}     {a2 = Above y}     h  ia1         =
  ≤-trans (true-reflects (≤-reflects y x) h) ia1
i-thinner-sem {a1 = Below x}     {a2 = Above y}     h  ia1         = absurd h
i-thinner-sem {a1 = Between x y} {a2 = Above z}     h  (iax , _)   =
  ≤-trans (true-reflects (≤-reflects z x) h) iax
i-thinner-sem {a1 = AllN}        {a2 = Above x}     h  ia1         = absurd h
i-thinner-sem {a1 = Above x}     {a2 = Below y}     h  ia1         = absurd h
i-thinner-sem {a1 = Below x}     {a2 = Below y}     h  ia1         =
  ≤-trans ia1 (true-reflects (≤-reflects x y) h)
i-thinner-sem {a1 = Between x y} {a2 = Below z}     h  (_ , iay)   =
  ≤-trans iay (true-reflects (≤-reflects y z) h)
i-thinner-sem {a1 = AllN}        {a2 = Below x}     h  ia1         = absurd h
i-thinner-sem {a1 = Above x}     {a2 = Between y z} h  ia1         = absurd h
i-thinner-sem {a1 = Below x}     {a2 = Between y z} h  ia1         = absurd h
i-thinner-sem {a1 = Between x y} {a2 = Between z w} h  (iax , iay) =
  let hh = and-true-≃ {x = z ≤ᵇ x} {y = y ≤ᵇ w} $ is-true≃is-trueₚ $ h in
    ≤-trans (true-reflects (≤-reflects z x) (is-true≃is-trueₚ ⁻¹ $ hh .fst)) iax
  , ≤-trans iay (true-reflects (≤-reflects y w) (is-true≃is-trueₚ ⁻¹ $ hh .snd))
i-thinner-sem {a1 = AllN}        {a2 = Between x y} h  ia1         = absurd h
i-thinner-sem {a1 = Above x}     {a2 = AllN}        tt ia1         = tt
i-thinner-sem {a1 = Below x}     {a2 = AllN}        h  ia1         = tt
i-thinner-sem {a1 = Between x y} {a2 = AllN}        h  ia1         = tt
i-thinner-sem {a1 = AllN}        {a2 = AllN}        h  ia1         = tt

open-intervals-no-dups : ∀ {s' l} s
                       → is-true (no-dups s l)
                       → is-true (no-dups (open-intervals s s') l)
open-intervals-no-dups          []            h = tt
open-intervals-no-dups {s'} {l} ((x , v) ∷ s) h =
  let hh = and-true-≃ {x = not (mem x l)} {y = no-dups s (x ∷ l)} $ is-true≃is-trueₚ $ h in
  is-true≃is-trueₚ ⁻¹ $ and-true-≃ {x = not (mem x l)} {y = no-dups (open-intervals s s') (x ∷ l)} ⁻¹ $
  (hh .fst) , (is-true≃is-trueₚ $ open-intervals-no-dups {s' = s'} s (is-true≃is-trueₚ ⁻¹ $ hh .snd))

i-over-approx-consistent : ∀ {n s s'}
                         → consistent s → consistent s'
                         → consistent (i-over-approx n s s')
i-over-approx-consistent {n = zero}           cs _ = tt
i-over-approx-consistent {n = suc _} {s} {s'} cs _ = open-intervals-no-dups {s' = s'} s cs

open module IIntSem = AIntCoreSem Interval AllN i-fromN i-add i-to-pred
                                  i-m
                                  (λ {e} → i-top-sem {e})
                                  (λ {g} {x} → i-fromN-sem {g} {x})
                                  (λ {g} {v} {e} → i-to-pred-sem {g} {v} {e})
                                  (λ {g} {v1} {v2} {x1} {x2} → i-add-sem {g} {v1} {v2} {x1} {x2})
                                  (λ {v} {x} {e} {e'} → i-subst-to-pred {v} {x} {e} {e'})

i-learn-from-success-aux-sem : ∀ {s n e g}
                             → consistent s
                             → ia i-m g (s→a s)
                             → g n < af g e
                             → ia i-m g (s→a' (i-learn-from-success-aux s n (a-af s e) (stlup s n)))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge with a-af s e | stlup s n | recall (a-af s) e | recall (stlup s) n
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Above x     | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = ias
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let y≤gn = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      afge≤x = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    ( y≤gn
    , (<≃≤pred {n = x} (<-weaken-z y x (<≃≱ ⁻¹ $ false-reflects (≤-reflects x y) (subst (is-true ∘ not) (eq ⁻¹) tt))) $
       <-≤-trans gn<afge afge≤x))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let y≤gn = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      afge≤x = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  (≤≃≯ $ true-reflects (≤-reflects x y) (is-true≃is-trueₚ ⁻¹ $ eq))
     (<-≤-trans (≤-<-trans y≤gn gn<afge) afge≤x)
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ = ias
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let afge≤x = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
      gn<x = <-≤-trans gn<afge afge≤x
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (<≃≤pred {n = x} (<-weaken-z (g n) x gn<x) $ gn<x)
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let ( y≤gn , gn≤z ) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      afge≤x = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    ( y≤gn
    , true-reflects (≤-reflects (g n) (min (pred x) z))
       (subst is-true (≤ᵇ-min {x = g n} {y = pred x} {z = z} ⁻¹)
         (is-true≃is-trueₚ ⁻¹ $ and-true-≃ {x = g n ≤ᵇ pred x} {y = g n ≤ᵇ z} ⁻¹ $
            (is-true≃is-trueₚ $ reflects-true (≤-reflects (g n) (pred x))
              (<≃≤pred {n = x} (<-weaken-z y x (<≃≱ ⁻¹ $ false-reflects (≤-reflects x y) (subst (is-true ∘ not) (eq ⁻¹) tt))) $
               <-≤-trans gn<afge afge≤x))
          , (is-true≃is-trueₚ $ reflects-true (≤-reflects (g n) z) gn≤z))))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let (y≤gn , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      afge≤x = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  (≤≃≯ $ true-reflects (≤-reflects x y) (is-true≃is-trueₚ ⁻¹ $ eq))
     (<-≤-trans (≤-<-trans y≤gn gn<afge) afge≤x)
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Below x     | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ =
  let afge≤x = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
      gn<x = <-≤-trans gn<afge afge≤x
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (<≃≤pred {n = x} (<-weaken-z (g n) x gn<x) $ gn<x)
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with y ≤ᵇ z | recall (y ≤ᵇ_) z
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let z≤gn = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (_ , afge≤y) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    ( z≤gn
    , (<≃≤pred {n = y} (<-weaken-z z y (<≃≱ ⁻¹ $ false-reflects (≤-reflects y z) (subst (is-true ∘ not) (eq ⁻¹) tt))) $
       <-≤-trans gn<afge afge≤y))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let z≤gn = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (_ , afge≤y) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  (≤≃≯ $ true-reflects (≤-reflects y z) (is-true≃is-trueₚ ⁻¹ $ eq))
    (≤-<-trans z≤gn (<-≤-trans gn<afge afge≤y))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with y ≤ᵇ z | recall (y ≤ᵇ_) z
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ = ias
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let (_ , afge≤y) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
      gn<y = <-≤-trans gn<afge afge≤y
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (<≃≤pred {n = y} (<-weaken-z (g n) y gn<y) $ gn<y)
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ with y ≤ᵇ z | recall (y ≤ᵇ_) z
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqyz ⟫ with y ≤ᵇ w | recall (y ≤ᵇ_) w
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqyz ⟫ | false | ⟪ eqyw ⟫ = ias
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqyz ⟫ | true  | ⟪ eqyw ⟫ =
  let (z≤gn , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (_ , afge≤y) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    ( z≤gn
    , (<≃≤pred {n = y} (<-weaken-z z y (<≃≱ ⁻¹ $ false-reflects (≤-reflects y z) (subst (is-true ∘ not) (eqyz ⁻¹) tt))) $
       <-≤-trans gn<afge afge≤y))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eqyz ⟫ =
  let (z≤gn , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (_ , afge≤y) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  (≤≃≯ $ true-reflects (≤-reflects y z) (is-true≃is-trueₚ ⁻¹ $ eqyz))
    (≤-<-trans z≤gn (<-≤-trans gn<afge afge≤y))
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | Between x y | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ =
  let (_ , afge≤y) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
      gn<y = <-≤-trans gn<afge afge≤y
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (<≃≤pred {n = y} (<-weaken-z (g n) y gn<y) $ gn<y)
i-learn-from-success-aux-sem {s} {n} {e} {g} cs ias gn<afge | AllN        | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = ias

i-learn-from-success-sem : ∀ {s b g}
                         → consistent s
                         → ia i-m g (s→a s)
                         → ia i-m g (QB b)
                         → ia i-m g (s→a' (i-learn-from-success s b))
i-learn-from-success-sem {b = BLt (ANum n) e}           cs ias iab = ias
i-learn-from-success-sem {b = BLt (AVar x) e}       {g} cs ias iab =
  i-learn-from-success-aux-sem {n = x} {e = e} cs ias (true-reflects (<-reflects (g x) (af g e)) iab)
i-learn-from-success-sem {b = BLt (APlus e₁ e₂) e₃}     cs ias iab = ias

i-learn-from-failure-aux-sem : ∀ {s n e g}
                             → consistent s
                             → ia i-m g (s→a s)
                             → af g e ≤ g n
                             → ia i-m g (s→a' (i-learn-from-failure-aux s n (a-af s e) (stlup s n)))
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn with a-af s e | stlup s n | recall (a-af s) e | recall (stlup s) n
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let x≤afge = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias) in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = ias
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let gn≤y = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      x≤afge = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  false-reflects (≤-reflects x y) (subst (is-true ∘ not) (eq ⁻¹) tt)
    (≤-trans x≤afge (≤-trans afge≤gn gn≤y))
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let gn≤y = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      x≤afge = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn , gn≤y)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ with z <ᵇ x | recall (z <ᵇ_) x
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqzx ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqzx ⟫ | false | ⟪ eqxy ⟫ =
  let (_ , gn≤z) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      x≤afge = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn , gn≤z)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqzx ⟫ | true  | ⟪ eqxy ⟫ = ias
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eqzx ⟫ =
  let (_ , gn≤z) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      x≤afge = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  (<≃≱ $ true-reflects (<-reflects z x) (is-true≃is-trueₚ ⁻¹ $ eqzx))
    (≤-trans x≤afge (≤-trans afge≤gn gn≤z))
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Above x     | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ =
  let x≤afge = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias) in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Below x     | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = ias
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ z | recall (x ≤ᵇ_) z
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let (x≤afge , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias) in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = ias
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ z | recall (x ≤ᵇ_) z
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  let gn≤z = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (x≤afge , _)  = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  false-reflects (≤-reflects x z) (subst (is-true ∘ not) (eq ⁻¹) tt)
    (≤-trans x≤afge (≤-trans afge≤gn gn≤z))
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  let gn≤z = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (x≤afge , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn , gn≤z)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ with w <ᵇ x | recall (w <ᵇ_) x
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqwx ⟫ with x ≤ᵇ z | recall (x ≤ᵇ_) z
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqwx ⟫ | false | ⟪ eqxz ⟫ =
  let (_ , gn≤w) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (x≤afge , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn , gn≤w)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqwx ⟫ | true  | ⟪ eqxz ⟫ = ias
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eqwx ⟫ =
  let (_ , gn≤w) = subst (λ q → ia i-m g (i-to-pred q (ANum (g n)))) eql (lookup-sem s ias)
      (x≤afge , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  (<≃≱ $ true-reflects (<-reflects w x) (is-true≃is-trueₚ ⁻¹ $ eqwx))
    (≤-trans x≤afge (≤-trans afge≤gn gn≤w))
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | Between x y | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ =
  let (x≤afge , _) = subst (λ q → ia i-m g (i-to-pred q (ANum (af g e)))) eqa (a-af-sound e ias)
    in
  a-upd-ia-all' {s = s} cs (λ {y} ny → transport (i-to-pred-sem {v = stlup s y} ⁻¹) (lookup-sem s ias))
    (≤-trans x≤afge afge≤gn)
i-learn-from-failure-aux-sem {s} {n} {e} {g} cs ias afge≤gn | AllN        | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = ias

i-learn-from-failure-sem : ∀ {s b g}
                         → consistent s
                         → ia i-m g (s→a s)
                         → ¬ ia i-m g (QB b)
                         → ia i-m g (s→a' (i-learn-from-failure s b))
i-learn-from-failure-sem {b = BLt (ANum n) e}          cs ias niab = ias
i-learn-from-failure-sem {b = BLt (AVar x) e}      {g} cs ias niab =
  i-learn-from-failure-aux-sem {n = x} {e = e} cs ias
    (≤≃≯ ⁻¹ $ false-reflects (<-reflects (g x) (af g e))
      (subst (is-true ∘ not) ((¬is-true≃is-falseₚ $ niab) ⁻¹) tt))
i-learn-from-failure-sem {b = BLt (APlus e e₁) e₃}     cs ias niab = ias

i-learn-from-success-aux-consistent : ∀ {s s' e n}
                                    → consistent s
                                    → i-learn-from-success-aux s n (a-af s e) (stlup s n) ＝ just s'
                                    → consistent s'
i-learn-from-success-aux-consistent {s} {e} {n} cs els with a-af s e | stlup s n | recall (a-af s) e | recall (stlup s) n
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Above x     | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = subst consistent (just-inj els) cs
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = absurd (nothing≠just els)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ = subst consistent (just-inj els) cs
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = absurd (nothing≠just els)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Below x     | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with y ≤ᵇ z | recall (y ≤ᵇ_) z
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = absurd (nothing≠just els)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with y ≤ᵇ z | recall (y ≤ᵇ_) z
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ = subst consistent (just-inj els) cs
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ with y ≤ᵇ z | recall (y ≤ᵇ_) z
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqyz ⟫ with y ≤ᵇ w | recall (y ≤ᵇ_) w
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqyz ⟫ | false | ⟪ eqyw ⟫ =
  subst consistent (just-inj els) cs
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqyz ⟫ | true  | ⟪ eqyw ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eqyz ⟫ = absurd (nothing≠just els)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | Between x y | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-success-aux-consistent {s} {e} {n} cs els | AllN        | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = subst consistent (just-inj els) cs

i-learn-from-success-consistent : ∀ {s b s'}
                                → consistent s
                                → i-learn-from-success s b ＝ just s'
                                → consistent s'
i-learn-from-success-consistent     {b = BLt (ANum n) e}       cs els = subst consistent (just-inj els) cs
i-learn-from-success-consistent {s} {b = BLt (AVar x) e}       cs els = i-learn-from-success-aux-consistent {s = s} {e = e} {n = x} cs els
i-learn-from-success-consistent     {b = BLt (APlus e₁ e₂) e₃} cs els = subst consistent (just-inj els) cs

i-learn-from-failure-aux-consistent : ∀ {s s' e n}
                                    → consistent s
                                    → i-learn-from-failure-aux s n (a-af s e) (stlup s n) ＝ just s'
                                    → consistent s'
i-learn-from-failure-aux-consistent {s} {e} {n} cs els with a-af s e | stlup s n | recall (a-af s) e | recall (stlup s) n
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Above y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = subst consistent (just-inj els) cs
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ = absurd (nothing≠just els)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Below y     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ with z <ᵇ x | recall (z <ᵇ_) x
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqzx ⟫ with x ≤ᵇ y | recall (x ≤ᵇ_) y
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqzx ⟫ | false | ⟪ eqxy ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqzx ⟫ | true  | ⟪ eqxy ⟫ =
  subst consistent (just-inj els) cs
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | Between y z | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eqzx ⟫ = absurd (nothing≠just els)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Above x     | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ = subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Below x     | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = subst consistent (just-inj els) cs
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ z | recall (x ≤ᵇ_) z
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Above z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ = subst consistent (just-inj els) cs
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ with x ≤ᵇ z | recall (x ≤ᵇ_) z
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eq ⟫ = absurd (nothing≠just els)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Below z     | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eq ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ with w <ᵇ x | recall (w <ᵇ_) x
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqwx ⟫ with x ≤ᵇ z | recall (x ≤ᵇ_) z
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqwx ⟫ | false | ⟪ eqxz ⟫ =
  subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | false | ⟪ eqwx ⟫ | true  | ⟪ eqxz ⟫ =
  subst consistent (just-inj els) cs
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | Between z w | ⟪ eqa ⟫ | ⟪ eql ⟫ | true  | ⟪ eqwx ⟫ = absurd (nothing≠just els)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | Between x y | AllN        | ⟪ eqa ⟫ | ⟪ eql ⟫ = subst consistent (just-inj els) (consistent-update {s = s} cs)
i-learn-from-failure-aux-consistent {s} {e} {n} cs els | AllN        | _           | ⟪ eqa ⟫ | ⟪ eql ⟫ = subst consistent (just-inj els) cs

i-learn-from-failure-consistent : ∀ {s b s'}
                                → consistent s
                                → i-learn-from-failure s b ＝ just s'
                                → consistent s'
i-learn-from-failure-consistent     {b = BLt (ANum n) e}       cs els = subst consistent (just-inj els) cs
i-learn-from-failure-consistent {s} {b = BLt (AVar x) e}       cs els = i-learn-from-failure-aux-consistent {s = s} {e = e} {n = x} cs els
i-learn-from-failure-consistent     {b = BLt (APlus e₁ e₂) e₃} cs els = subst consistent (just-inj els) cs

open module IntervalIntSem = AInt2Sem Interval AllN i-add i-fromN i-to-pred
                                      i-learn-from-success i-learn-from-failure
                                      i-join i-thinner i-over-approx
                                      i-choose-1 i-choose-2
                                      i-m
                                      (λ {e} → i-top-sem {e})
                                      (λ {v} {x} {e} {e'} → i-subst-to-pred {v} {x} {e} {e'})
                                      (λ {g} {x} → i-fromN-sem {g} {x})
                                      (λ {g} {v} {e} → i-to-pred-sem {g} {v} {e})
                                      (λ {g} {v1} {v2} {x1} {x2} → i-add-sem {g} {v1} {v2} {x1} {x2})
                                      (λ {a} {b} → i-join-thinner-1 {a} {b})
                                      (λ {a} {b} → i-join-thinner-2 {a} {b})
                                      (λ {a1} {a2} → i-thinner-sem {a1} {a2})
                                      (λ {n} {s} {s'} → i-over-approx-consistent {n} {s} {s'})
                                      (λ {s} {b} {s'} → i-learn-from-success-consistent {s} {b} {s'})
                                      (λ {s} {b} {s'} → i-learn-from-failure-consistent {s} {b} {s'})
                                      (λ {g} {n} {s} {s'} → i-over-approx-sem {g} {n} {s} {s'})
                                      (λ {s} {b} {g} → i-learn-from-success-sem {s} {b} {g})
                                      (λ {s} {b} {g} → i-learn-from-failure-sem {s} {b} {g})
