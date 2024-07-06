module Absint1 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Lang
open import State

module AInt
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  where

  open State.State A top

  -- abstract interpreter

  a-af : State → AExpr → A
  a-af s (ANum n)      = fromN n
  a-af s (AVar x)      = stlup s x
  a-af s (APlus e₁ e₂) = add (a-af s e₁) (a-af s e₂)

  s→a : State → Assert
  s→a []            = QTrue
  s→a ((x , a) ∷ t) = QConj (to-pred a (AVar x)) (s→a t)

  ab1 : Instr → State → AnInstr × State
  ab1 (Assign x e) s =
    (AnPre (s→a s) (AnAssign x e)) , stupd x (a-af s e) s
  ab1 (Seq i₁ i₂)  s =
    let (ai₁ , s₁) = ab1 i₁ s
        (ai₂ , s₂) = ab1 i₂ s₁
     in
    AnSeq ai₁ ai₂ , s₂
  ab1 (While b i)  s =
    let (ai , _) = ab1 i [] in
    AnWhile b (s→a []) ai , []

module AIntSem
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  (m : String → List ℕ → 𝒰) {- TODO prop ? -}

  (top-sem : ∀ e → to-pred top e ＝ QTrue)
  (subst-to-pred : ∀ v x e e' → xsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  (fromN-sem : ∀ g x → ia m g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ g v e → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (a-add-sem : ∀ g v1 v2 x1 x2
            → ia m g (to-pred v1 (ANum x1))
            → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))
  where

  open State.State A top
  open AInt A top fromN add to-pred

  lookup-sem : ∀ {g} s → ia m g (s→a s)
             → ∀ {x} → ia m g (to-pred (stlup s x) (ANum (g x)))
  lookup-sem {g} []            tt            = subst (ia m g) (top-sem (ANum (g _)) ⁻¹) tt
  lookup-sem {g} ((y , v) ∷ s) (h1 , h2) {x} =
    elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s x) (ANum (g x)))}
          (λ p → transport (to-pred-sem g v (AVar y) ∙ ap (λ q → ia m g (to-pred v (ANum (g q)))) (p ⁻¹)) h1)
          (λ _ → lookup-sem s h2)
          (x ≟ y)

  xsubst-no-occur : ∀ {x l e} s
                  → is-true (no-dups s (x ∷ l))
                  → xsubst x e (s→a s) ＝ s→a s
  xsubst-no-occur             []            _ = refl
  xsubst-no-occur {x} {l} {e} ((y , v) ∷ s)   =
    elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l) and no-dups s (y ∷ x ∷ l))
                   → QConj (xsubst x e (to-pred v (AVar y))) (xsubst x e (s→a s)) ＝ QConj (to-pred v (AVar y)) (s→a s)}
      (λ p c → absurd c)
      (λ ¬p h → let h' = and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ x ∷ l)} $ is-true-≃ $ h in
                ap² QConj
                  (  subst-to-pred v x (AVar y) e
                   ∙ ap (to-pred v) (elimᵈ {C = λ q → (if ⌊ q ⌋ then e else AVar y) ＝ AVar y}
                                           (λ p → absurd (¬p p))
                                           (λ _ → refl)
                                           (x ≟ y)))
                  (xsubst-no-occur {l = y ∷ l} s (is-true-≃ ⁻¹ $ subst is-trueₚ (no-dups-transpose-head {s = s}) (h' .snd))))
      (x ≟ y)

  subst-no-dups : ∀ {g v x e l} s
                → is-true (no-dups s l)
                → ia m g (s→a s)
                → ia m g (to-pred v (ANum (af g e)))
                → ia m g (xsubst x e (s→a (stupd x v s)))
  subst-no-dups {g} {v} {x} {e}     []            h1 h2 h3 =
      subst (ia m g) (subst-to-pred _ _ (AVar _) _ ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred v (if ⌊ q ⌋ then e else AVar x))}
                                                              (λ _ → transport (to-pred-sem g v e ⁻¹) h3)
                                                              (λ ¬p → absurd (¬p refl))
                                                              (x ≟ x)) , tt
  subst-no-dups {g} {v} {x} {e} {l} ((y , w) ∷ s) h1 (h2 , h3) h4 =
    let h5 = (and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ l)} $ is-true-≃ $ h1) .snd in
    elimᵈ {C = λ q → ia m g (xsubst x e (s→a (if ⌊ q ⌋ then (y , v) ∷ s else (y , w) ∷ stupd x v s)))}
      (λ p  →   subst (ia m g) (subst-to-pred v x (AVar y) e ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred v (if ⌊ q ⌋ then e else AVar y))}
                                                                        (λ _ → transport (to-pred-sem g v e ⁻¹) h4)
                                                                        (λ ¬p → absurd (¬p p))
                                                                        (x ≟ y))
              , subst (ia m g) (xsubst-no-occur s (is-true-≃ ⁻¹ $ subst (λ q → is-trueₚ (no-dups s (q ∷ l))) (p ⁻¹) h5) ⁻¹) h3)
      (λ ¬p →   subst (ia m g) (subst-to-pred w x (AVar y) e ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred w (if ⌊ q ⌋ then e else AVar y))}
                                                                        (λ p → absurd (¬p p))
                                                                        (λ _ → h2)
                                                                        (x ≟ y))
              , subst-no-dups s (is-true-≃ ⁻¹ $ h5) h3 h4)
      (x ≟ y)

  subst-consistent : ∀ {s g v x e}
                   → consistent s
                   → ia m g (s→a s)
                   → ia m g (to-pred v (ANum (af g e)))
                   → ia m g (xsubst x e (s→a (stupd x v s)))
  subst-consistent {s} = subst-no-dups s

  ab1-pc : ∀ {i' s s'} i
         → ab1 i s ＝ (i' , s')
         → ∀ {g a} → ia m g (s→a s) → ia m g (pc i' a)
  ab1-pc     (Assign x e) h1 {g} {a} h2 =
    subst (λ q → ia m g (pc q a)) (ap fst h1) h2
  ab1-pc {s} (Seq i₁ i₂)  h1 {g} {a} h2 =
    subst (λ q → ia m g (pc q a)) (ap fst h1) $
    ab1-pc i₁ refl h2
  ab1-pc     (While b i)  h1 {g} {a} h2 =
    subst (λ q → ia m g (pc q a)) (ap fst h1) tt

  a-af-sound : ∀ {s g} e
             → ia m g (s→a s)
             → ia m g (to-pred (a-af s e) (ANum (af g e)))
  a-af-sound     (ANum n)      h = fromN-sem _ n
  a-af-sound {s} (AVar x)      h = lookup-sem s h
  a-af-sound {s} (APlus e₁ e₂) h = a-add-sem _ (a-af s e₁) (a-af s e₂) (af _ e₁) (af _ e₂) (a-af-sound e₁ h) (a-af-sound e₂ h)

  ab1-correct : ∀ {i' s s'} i
              → consistent s
              → ab1 i s ＝ (i' , s')
              → valid m (vc i' (s→a s')) × consistent s'
  ab1-correct {i'} {s} (Assign x e) h1 h2 =
    subst (λ q → valid m (vc i' (s→a q)) × consistent q) (ap snd h2) $
      subst (λ q → valid m (vc q (s→a (stupd x (a-af s e) s)))) (ap fst h2)
            ((λ g z → subst-consistent {s = s} h1 z (a-af-sound e z)) , tt)
    , (consistent-update {s = s} h1)
  ab1-correct {i'} {s} (Seq i₁ i₂)  h1 h2 =
    let (ih11 , ih12) = ab1-correct {s = s} i₁ h1 refl
        (ih21 , ih22) = ab1-correct {s = ab1 i₁ s .snd} i₂ ih12 refl
      in
    subst (λ q → valid m (vc i' (s→a q)) × consistent q) (ap snd h2) $
      subst (λ q → valid m (vc q (s→a (ab1 i₂ (ab1 i₁ s .snd) .snd)))) (ap fst h2)
            (valid-cat ((vc (ab1 i₁ s .fst) (pc (ab1 i₂ (ab1 i₁ s .snd) .fst) (s→a (ab1 i₂ (ab1 i₁ s .snd) .snd)))))
                       (vc-monotonic (λ g x → ab1-pc i₂ refl x)
                          (ab1 i₁ s .fst) ih11 .fst)
                       ih21)
    , ih22
  ab1-correct {i'} {s} (While b i)  h1 h2 =
    let (ih1 , ih2) = ab1-correct {s = []} i tt refl
        qq = vc-monotonic {p2 = QTrue} (λ _ _ → tt) (ab1 i [] .fst) ih1
      in
    subst (λ q → valid m (vc i' (s→a q)) × consistent q) (ap snd h2) $
      subst (λ q → valid m (vc q QTrue)) (ap fst h2)
            ( (λ g x → ab1-pc i refl tt)
            , (λ _ _ → tt)
            , qq .fst)
    , tt

  ab1-clean : ∀ {i' s s'} i
            → ab1 i s ＝ (i' , s') → cleanup i' ＝ i
  ab1-clean (Assign x r) h =
    subst (λ q → cleanup q ＝ Assign x r) (ap fst h) refl
  ab1-clean (Seq i₁ i₂)  h =
    subst (λ q → cleanup q ＝ Seq i₁ i₂) (ap fst h) $
    ap² Seq (ab1-clean i₁ refl) (ab1-clean i₂ refl)
  ab1-clean (While b i)  h =
    subst (λ q → cleanup q ＝ While b i) (ap fst h) $
    ap (While b) (ab1-clean i refl)

  lookup-sem2 : ∀ {g l} s
              → is-true (no-dups s l)
              → (∀ x → is-true (not (mem x l)) → ia m g (to-pred (stlup s x) (AVar x)))
              → ia m g (s→a s)
  lookup-sem2         []            h p = tt
  lookup-sem2 {g} {l} ((x , v) ∷ s) h p =
    let hh = and-true-≃ {x = not (mem x l)} {y = no-dups s (x ∷ l)} $
             is-true-≃ $ h in
      elimᵈ {C = λ q → (is-true (not (mem x l)) →
                        ia m g (to-pred (if ⌊ q ⌋ then v else stlup s x) (AVar x))) →
                 ia m g (to-pred v (AVar x)) }
            (λ _ f → f (is-true-≃ ⁻¹ $ hh .fst))
            (λ ¬p → absurd (¬p refl))
            (x ≟ x) (p x)
    , lookup-sem2 {l = x ∷ l} s (is-true-≃ ⁻¹ $ hh .snd)
        λ y my → elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l)) →
                                   ia m g (to-pred (stlup s y) (AVar y)) }
                       (λ hp my′  → absurd my′)
                       (λ ¬hp my′ → elimᵈ
                                     {C =
                                      λ q → (is-true (not (mem y l)) →
                                             ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))) →
                                            ia m g (to-pred (stlup s y) (AVar y))}
                                     (λ ep py  → absurd (¬hp (ep ⁻¹)))
                                     (λ ¬ep py → py my′)
                                     (y ≟ x) (p y))
                       (x ≟ y) my

-- testing

data OE : 𝒰 where
  Even Odd OETop : OE

OE-fromN : ℕ → OE
OE-fromN n = if odd n then Odd else Even

addOE : OE → OE → OE
addOE Even  Even  = Even
addOE Even  Odd   = Odd
addOE Odd   Even  = Odd
addOE Odd   Odd   = Even
addOE _     _     = OETop

OE-to-pred : OE → AExpr → Assert
OE-to-pred Even  e = QPred "even" (e ∷ [])
OE-to-pred Odd   e = QPred "odd" (e ∷ [])
OE-to-pred OETop e = QTrue

open module OEState = State.State OE OETop
open module OEInt = AInt OE OETop OE-fromN addOE OE-to-pred

testprog : Instr
testprog = Seq (Assign "x" (APlus (AVar "x") (AVar "y")))
               (Assign "y" (APlus (AVar "y") (ANum 1)))

testst : State
testst = ("x" , Even) ∷ ("y" , Odd) ∷ []

testres : AnInstr × State
testres = AnSeq (AnPre (QConj (QPred "even" (AVar "x" ∷ []))
                        (QConj (QPred "odd" (AVar "y" ∷ [])) QTrue))
                       (AnAssign "x" (APlus (AVar "x") (AVar "y"))))
                (AnPre (QConj (QPred "odd" (AVar "x" ∷ []))
                        (QConj (QPred "odd" (AVar "y" ∷ [])) QTrue))
                       (AnAssign "y" (APlus (AVar "y") (ANum 1))))
       , ("x" , Odd) ∷ ("y" , Even) ∷ []

testab1 : ab1 testprog testst ＝ testres
testab1 = refl

OE-top-sem : ∀ e → OE-to-pred OETop e ＝ QTrue
OE-top-sem e = refl

OE-subst-to-pred : ∀ v x e e' → xsubst x e' (OE-to-pred v e) ＝ OE-to-pred v (asubst x e' e)
OE-subst-to-pred Even  x e e' = refl
OE-subst-to-pred Odd   x e e' = refl
OE-subst-to-pred OETop x e e' = refl
