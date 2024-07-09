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
open import AbsintCore

module AInt
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  where

  open State.State A top
  open AbsintCore.AIntCore A top fromN add to-pred

  -- abstract interpreter
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

  (m : String → List ℕ → 𝒰)

  (top-sem : ∀ {e} → to-pred top e ＝ QTrue)
  (fromN-sem : ∀ {g x} → ia m g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ {g v e} → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (a-add-sem : ∀ {g v1 v2 x1 x2}
            → ia m g (to-pred v1 (ANum x1))
            → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))
  (subst-to-pred : ∀ {v x e e'} → xsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  where

  open State.State A top
  open AbsintCore.AIntCore A top fromN add to-pred
  open AInt A top fromN add to-pred
  open AbsintCore.AIntCoreSem A top fromN add to-pred m top-sem fromN-sem to-pred-sem a-add-sem subst-to-pred

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
