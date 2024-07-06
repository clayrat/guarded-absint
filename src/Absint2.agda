module Absint2 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.Maybe renaming (rec to recᵐ ; elim to elimᵐ)
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Lang
open import State

-- TODO better decoupling
-- we need s→a, a-af, lookup-sem, lookup-sem2 from Absint1
open import Absint1

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
  open AInt A top fromN add to-pred

  s→a' : Maybe State → Assert
  s→a' (just s) = s→a s
  s→a' nothing  = QFalse

  join-state : State → State → State
  join-state []             s2 = []
  join-state ((x , v) ∷ s1) s2 = stupd x (join v (stlup s2 x)) (join-state s1 s2)

  join-state-m : State → Maybe State → State
  join-state-m s1 (just s2) = join-state s1 s2
  join-state-m s1  nothing  = s1

  mark : Instr → AnInstr
  mark (Assign x e) = AnPre QFalse (AnAssign x e)
  mark (Seq i₁ i₂)  = AnSeq (mark i₁) (mark i₂)
  mark (While b i)  = AnWhile b QFalse (mark i)

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

  do-annot : (State → AnInstr × Maybe State)
           → BExpr → State → Instr → AnInstr
  do-annot ab b s i = recᵐ (mark i) (λ s′ → ab s′ .fst) (learn-from-success s b)

  ab2 : Instr → State → AnInstr × Maybe State
  ab2 (Assign x e) s = AnPre (s→a s) (AnAssign x e) , just (stupd x (a-af s e) s)
  ab2 (Seq i₁ i₂)  s = let (a_i1 , s1) = ab2 i₁ s in
                       recᵐ ((AnSeq a_i1 (mark i₂)) , nothing)
                            (λ s1′ → let (a_i2 , s2) = ab2 i₂ s1′ in
                                     (AnSeq a_i1 a_i2) , s2)
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

  (top-sem : ∀ e → to-pred top e ＝ QTrue)
  (subst-to-pred : ∀ v x e e' → xsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  (fromN-sem : ∀ g x → ia m g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ g v e → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (a-add-sem : ∀ g v1 v2 x1 x2
            → ia m g (to-pred v1 (ANum x1))
            → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))
  (learn-from-success-sem : ∀ s b g (s→a : St A → Assert) (s→a' : Maybe (St A) → Assert) (consistent : St A → 𝒰)
                          → consistent s
                          → ia m g (s→a s) → ia m g (QB b)
                          → ia m g (s→a' (learn-from-success s b)))
  (learn-from-failure-sem : ∀ s b g (s→a : St A → Assert) (s→a' : Maybe (St A) → Assert) (consistent : St A → 𝒰)
                          → consistent s
                          → ia m g (s→a s) → ¬ ia m g (QB b)
                          → ia m g (s→a' (learn-from-failure s b)))
  (over-approx-sem : ∀ g n s s' (s→a : St A → Assert)
                   → ia m g (s→a s)
                   → ia m g (s→a (over-approx n s s')))
  (join-thinner-1 : ∀ a b → is-true (thinner a (join a b)))
  (join-thinner-2 : ∀ a b → is-true (thinner b (join a b)))
  (thinner-sem : ∀ a1 a2 → is-true (thinner a1 a2)
               → ∀ g e → ia m g (to-pred a1 e) → ia m g (to-pred a2 e))
  (over-approx-consistent : ∀ n s s' (consistent : St A → 𝒰)
                          → consistent s → consistent s'
                          → consistent (over-approx n s s'))
  (learn_from_success_consistent : ∀ s b s' (consistent : St A → 𝒰)
                                 → consistent s
                                 → learn-from-success s b ＝ just s'
                                 → consistent s')
  (learn_from_failure_consistent : ∀ s b s' (consistent : St A → 𝒰)
                                 → consistent s
                                 → learn-from-failure s b ＝ just s'
                                 → consistent s')
  where

  open State.State A top
  open AInt2 A top add fromN to-pred learn-from-success learn-from-failure join thinner over-approx choose-1 choose-2
  open AInt A top fromN add to-pred
  open AIntSem A top fromN add to-pred m top-sem subst-to-pred fromN-sem to-pred-sem a-add-sem

  join-safe-1 : ∀ {g a b x} → ia m g (to-pred a x) → ia m g (to-pred (join a b) x)
  join-safe-1 {g} {a} {b} {x} iax = thinner-sem a (join a b) (join-thinner-1 a b) g x iax

  join-safe-2 : ∀ {g a b x} → ia m g (to-pred b x) → ia m g (to-pred (join a b) x)
  join-safe-2 {g} {a} {b} {x} iax = thinner-sem b (join a b) (join-thinner-2 a b) g x iax

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
    subst (ia m g) (top-sem (AVar y) ⁻¹) tt
  upd-others {g} {x} {e} ((z , v) ∷ s)                   =
    elimᵈ {C = λ q → ia m g (s→a (if ⌊ q ⌋ then (z , e) ∷ s else (z , v) ∷ stupd x e s))
                   → {y : String} → x ≠ y
                   → ia m g (to-pred (if ⌊ y ≟ z ⌋ then v else stlup s y) (AVar y))}
          (λ p  iax {y} ne → elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))}
                                   (λ eq → absurd (ne (p ∙ eq ⁻¹)))
                                   (λ _  → transport (to-pred-sem g (stlup s y) (AVar y) ⁻¹) (lookup-sem s (iax .snd)))
                                   (y ≟ z) )
          (λ ¬p iax {y} ne → elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))}
                                   (λ eq → subst (λ q → ia m g (to-pred v (AVar q))) (eq ⁻¹) (iax .fst))
                                   (λ _  → upd-others s (iax .snd) ne)
                                   (y ≟ z) )
          (x ≟ z)

  a-upd-ia-all : ∀ {g l x e} s → is-true (no-dups s l)
               → (∀ {y} → y ≠ x → is-true (not (mem y l))
                  → ia m g (to-pred (stlup s y) (AVar y)))
               → ia m g (to-pred e (AVar x))
               → ia m g (s→a (stupd x e s))
  a-upd-ia-all []            cs f h = h , tt
  a-upd-ia-all {g} {l} {x} {e} ((z , v) ∷ s) cs     =
    elimᵈ {C = λ q → ({y : String} → y ≠ x → is-true (not (mem y l))
                      → ia m g (to-pred (if ⌊ y ≟ z ⌋ then v else stlup s y) (AVar y)))
                   → ia m g (to-pred e (AVar x))
                   → ia m g (s→a (if ⌊ q ⌋ then (z , e) ∷ s else (z , v) ∷ stupd x e s)) }
          (λ p  ias iax →   (subst (λ q → ia m g (to-pred e (AVar q))) p iax)
                          , (lookup-sem2 {l = z ∷ l} s
                             (is-true-≃ ⁻¹ $ (and-true-≃ {x = not (mem z l)} {y = no-dups s (z ∷ l)} $ is-true-≃ $ cs) .snd)
                             λ y h →
                               let hh = and-true-≃ {x = not ⌊ z ≟ y ⌋} {y = not (mem y l)} $
                                        subst is-trueₚ (not-or ⌊ z ≟ y ⌋ (mem y l)) (is-true-≃ $ h) in
                               elimᵈ {C = λ q → (y ≠ x →
                                                 is-true (not (mem y l)) →
                                                 ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))) →
                                                ia m g (to-pred (stlup s y) (AVar y))}
                                     (λ e  _ → absurd (elimᵈ {C = λ q → is-trueₚ (not ⌊ q ⌋) → ⊥}
                                                             (λ _     → false≠true)
                                                             (λ ¬e′ _ → ¬e′ (e ⁻¹))
                                                             (z ≟ y) (hh .fst)))
                                     (λ ¬e f → f (λ p′ → ¬e (p′ ∙ p)) (is-true-≃ ⁻¹ $ hh .snd))
                                     (y ≟ z)
                                     (ias {y})))
          (λ ¬p ias iax → let hh = and-true-≃ {x = not (mem z l)} {y = no-dups s (z ∷ l)} $ is-true-≃ $ cs in
                            elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s z) (AVar z))
                                           → ia m g (to-pred v (AVar z))}
                                  (λ _  → id)
                                  (λ ¬c → absurd (¬c refl))
                                  (z ≟ z)
                                  (ias (λ w → ¬p (w ⁻¹)) (is-true-≃ ⁻¹ $ hh .fst))
                          , a-upd-ia-all {l = z ∷ l} s (is-true-≃ ⁻¹ $ hh .snd)
                               (λ {y} ne h → let h′ = and-true-≃ {x = not ⌊ z ≟ y ⌋} {y = not (mem y l)} $
                                                      is-true-≃ $ subst is-true (not-or ⌊ z ≟ y ⌋ (mem y l)) h in
                                             elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))
                                                            → ia m g (to-pred (stlup s y) (AVar y))}
                                                   (λ yz → absurd (elimᵈ {C = λ q → is-trueₚ (not ⌊ q ⌋) → ⊥}
                                                                         (λ _ → false≠true) (λ ¬e′ _ → ¬e′ (yz ⁻¹))
                                                                         (z ≟ y) (h′ .fst)))
                                                   (λ ¬yz → id)
                                                   (y ≟ z)
                                                   (ias ne (is-true-≃ ⁻¹ $ h′ .snd)))
                               iax)
          (x ≟ z)

  a-upd-ia-all' : ∀ {g s x e} → consistent s
                → (∀ {y} → y ≠ x → ia m g (to-pred (stlup s y) (AVar y)))
                → ia m g (to-pred e (AVar x))
                → ia m g (s→a (stupd x e s))
  a-upd-ia-all' {s} cs ias = a-upd-ia-all s cs (λ {y} ne _ → ias ne)

  join-state-consistent : ∀ {s2} s1 → consistent (join-state s1 s2)
  join-state-consistent      []             = tt
  join-state-consistent {s2} ((x , v) ∷ s1) = consistent-update {s = join-state s1 s2} (join-state-consistent s1)

  join-state-safe-1 : ∀ {g s2} s1 → ia m g (s→a s1) → ia m g (s→a (join-state s1 s2))
  join-state-safe-1          []             tt          = tt
  join-state-safe-1 {g} {s2} ((x , v) ∷ s1) (iax , ias) =
    a-upd-ia-all' {s = join-state s1 s2}
      (join-state-consistent s1)
      (λ {y} ne → transport (to-pred-sem g (stlup (join-state s1 s2) y) (AVar y) ⁻¹)
                            (lookup-sem (join-state s1 s2) (join-state-safe-1 s1 ias)))
      (join-safe-1 iax)

  join-state-safe-2 : ∀ {g s2} s1 → ia m g (s→a s2) → ia m g (s→a (join-state s1 s2))
  join-state-safe-2          []             iax = tt
  join-state-safe-2 {g} {s2} ((x , v) ∷ s1) iax =
    a-upd-ia-all' {s = join-state s1 s2}
      (join-state-consistent s1)
      (λ {y} ne → transport (to-pred-sem g (stlup (join-state s1 s2) y) (AVar y) ⁻¹)
                            (lookup-sem (join-state s1 s2) (join-state-safe-2 s1 iax)))
      (join-safe-2 (transport (to-pred-sem g (stlup s2 x) (AVar x) ⁻¹)
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
open module IInt = AInt Interval AllN i-fromN i-add i-to-pred

-- TODO upstream

minᵇ : ℕ → ℕ → ℕ
minᵇ x y = if x ≤ᵇ y then x else y

maxᵇ : ℕ → ℕ → ℕ
maxᵇ x y = if x ≤ᵇ y then y else x

i-learn-from-success-aux : State → String → Interval → Interval → Maybe State
i-learn-from-success-aux s n (Below x)     (Above y)     = if x ≤ᵇ y then nothing
                                                                     else just (stupd n (Between y (pred x)) s)
i-learn-from-success-aux s n (Below x)     (Below y)     = just (if x ≤ᵇ y then stupd n (Below (pred x)) s
                                                                           else s)
i-learn-from-success-aux s n (Below x)     (Between y z) = if x ≤ᵇ y then nothing
                                                                     else just (stupd n (Between y (minᵇ (pred x) z)) s)
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
i-join (Above x)     (Above y)     = Above (minᵇ x y)
i-join (Above x)     (Between y _) = Above (minᵇ x y)
i-join (Below x)     (Below y)     = Below (maxᵇ x y)
i-join (Below x)     (Between _ z) = Below (maxᵇ x z)
i-join (Between x _) (Above z)     = Above (minᵇ x z)
i-join (Between _ y) (Below z)     = Below (maxᵇ y z)
i-join (Between x y) (Between z w) = Between (minᵇ x z) (maxᵇ y w)
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

i-1 : Instr
i-1 = While (BLt (AVar "x") (ANum 10))
            (Assign "x" (APlus (AVar "x") (ANum 1)))

s-1 : State
s-1 = ("x" , i-fromN 0) ∷ []

res-1 : AnInstr × Maybe State
res-1 =   AnWhile (BLt (AVar "x") (ANum 10))
                  (QConj
                    (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                           (QPred "leq" (AVar "x" ∷ ANum 10 ∷ [])))
                    QTrue)
                  (AnPre (QConj
                           (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                  (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                           QTrue)
                         (AnAssign "x" (APlus (AVar "x") (ANum 1))))
        , just (("x" , Between 10 10) ∷ [])

test-1 : ab2 i-1 s-1 ＝ res-1
test-1 = refl

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

i-m-aux : List ℕ → 𝒰
i-m-aux (x ∷ y ∷ []) = x ≤ y
i-m-aux _            = ⊥

i-m : String → List ℕ → 𝒰
i-m s l = if s =ₛ "leq" then i-m-aux l else ⊥
