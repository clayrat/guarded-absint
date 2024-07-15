module Bertot.Absint1 where

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
open import Data.Reflects
open import Data.Sum

open import Bertot.State as S
open import Bertot.Lang 
open import Bertot.AbsintCore as AC

module AInt
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  where

  open S.State A top
  open AC.AIntCore A top fromN add to-pred

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
  (subst-to-pred : ∀ {v x e e'} → qsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  where

  open S.State A top
  open AC.AIntCore A top fromN add to-pred
  open AInt A top fromN add to-pred
  open AC.AIntCoreSem A top fromN add to-pred m top-sem fromN-sem to-pred-sem a-add-sem subst-to-pred

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

oe-fromN : ℕ → OE
oe-fromN n = if odd n then Odd else Even

oe-add : OE → OE → OE
oe-add Even  Even  = Even
oe-add Even  Odd   = Odd
oe-add Odd   Even  = Odd
oe-add Odd   Odd   = Even
oe-add _     _     = OETop

oe-to-pred : OE → AExpr → Assert
oe-to-pred Even  e = QPred "even" (e ∷ [])
oe-to-pred Odd   e = QPred "odd" (e ∷ [])
oe-to-pred OETop e = QTrue

open module OEState = S.State OE OETop
open module OEInt = AInt OE OETop oe-fromN oe-add oe-to-pred

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

-- properties

oe-m-aux : List ℕ → Bool → 𝒰
oe-m-aux (x ∷ []) true  = is-true (even x)
oe-m-aux (x ∷ []) false = is-true (odd x)
oe-m-aux _        _     = ⊥

oe-m : String → List ℕ → 𝒰
oe-m s l = if ⌊ s ≟ "even" ⌋ then oe-m-aux l true else if ⌊ s ≟ "odd" ⌋ then oe-m-aux l false else ⊥

oe-top-sem : ∀ {e} → oe-to-pred OETop e ＝ QTrue
oe-top-sem = refl

oe-fromN-sem : ∀ {g x} → ia oe-m g (oe-to-pred (oe-fromN x) (ANum x))
oe-fromN-sem {g} {x} with odd x | recall odd x
... | true  | ⟪ eq ⟫ = is-true≃is-trueₚ ⁻¹ $ eq
... | false | ⟪ eq ⟫ = is-true≃is-trueₚ ⁻¹ $ ap not eq

oe-to-pred-sem : ∀ {g v e} → ia oe-m g (oe-to-pred v e) ＝ ia oe-m g (oe-to-pred v (ANum (af g e)))
oe-to-pred-sem {v = Even}  = refl
oe-to-pred-sem {v = Odd}   = refl
oe-to-pred-sem {v = OETop} = refl

oe-add-sem : ∀ {g v1 v2 x1 x2}
            → ia oe-m g (oe-to-pred v1 (ANum x1))
            → ia oe-m g (oe-to-pred v2 (ANum x2))
            → ia oe-m g (oe-to-pred (oe-add v1 v2) (ANum (x1 + x2)))
oe-add-sem {v1 = Even}  {v2 = Even}  {x1} {x2} ia1 ia2 =
  subst (is-true ∘ not) (odd-+ x1 x2 ⁻¹) $
  subst is-true (not-xor-l (odd x1) (odd x2) ⁻¹) $
  reflects-true (reflects-xor {x = not (odd x1)} {y = odd x2}) $
  not-invol (odd x1) ∙ not-inj ((is-true≃is-trueₚ $ ia1) ∙ (is-true≃is-trueₚ $ ia2) ⁻¹)
oe-add-sem {v1 = Even}  {v2 = Odd}   {x1} {x2} ia1 ia2 =
  subst (is-true) (odd-+ x1 x2 ⁻¹) $
  reflects-true (reflects-xor {x = odd x1} {y = odd x2}) $
  (is-true≃is-trueₚ $ ia1) ∙ (is-true≃is-trueₚ $ ia2) ⁻¹
oe-add-sem {v1 = Even}  {v2 = OETop}           ia1 ia2 = tt
oe-add-sem {v1 = Odd}   {v2 = Even}  {x1} {x2} ia1 ia2 =
  subst (is-true) (odd-+ x1 x2 ⁻¹) $
  reflects-true (reflects-xor {x = odd x1} {y = odd x2}) $
  ap not (is-true≃is-trueₚ $ ia1) ∙ not-inj ((is-true≃is-trueₚ $ ia2) ⁻¹)
oe-add-sem {v1 = Odd}   {v2 = Odd}   {x1} {x2} ia1 ia2 =
  subst (is-true ∘ not) (odd-+ x1 x2 ⁻¹) $
  subst is-true (not-xor-l (odd x1) (odd x2) ⁻¹) $
  reflects-true (reflects-xor {x = not (odd x1)} {y = odd x2}) $
  not-invol (odd x1) ∙ (is-true≃is-trueₚ $ ia1) ∙ (is-true≃is-trueₚ $ ia2) ⁻¹
oe-add-sem {v1 = Odd}   {v2 = OETop}           ia1 ia2 = tt
oe-add-sem {v1 = OETop} {v2 = Even}            ia1 ia2 = tt
oe-add-sem {v1 = OETop} {v2 = Odd}             ia1 ia2 = tt
oe-add-sem {v1 = OETop} {v2 = OETop}           ia1 ia2 = tt

oe-subst-to-pred : ∀ {v x e e'}
                 → qsubst x e' (oe-to-pred v e) ＝ oe-to-pred v (asubst x e' e)
oe-subst-to-pred {v = Even}  = refl
oe-subst-to-pred {v = Odd}   = refl
oe-subst-to-pred {v = OETop} = refl

open module OEIntSem = AIntSem OE OETop oe-fromN oe-add oe-to-pred
                               oe-m
                               (λ {e} → oe-top-sem {e})
                               (λ {g} {x} → oe-fromN-sem {g} {x})
                               (λ {g} {v} {e} → oe-to-pred-sem {g} {v} {e})
                               (λ {g} {v1} {v2} {x1} {x2} → oe-add-sem {g} {v1} {v2} {x1} {x2})
                               (λ {v} {x} {e} {e'} → oe-subst-to-pred {v} {x} {e} {e'})
