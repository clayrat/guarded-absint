{-# OPTIONS --safe #-}
module SPA.FMap where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.Maybe.Instances.Map.Properties
open import Data.Maybe.Instances.Bind.Properties
open import Data.Sum as Sum
open import Data.These as These

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

-- finite maps

private variable
  ℓᵃ ℓᵇ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

record FMap (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) : 𝒰 (ℓᵃ ⊔ ℓᵇ) where
  constructor mkfmap
  field
    fun : A → Maybe B
    dom : LFSet A
    nde : ∀ {x} → x ∉ dom ≃ fun x ＝ nothing

open FMap public

unquoteDecl FMap-Iso = declare-record-iso FMap-Iso (quote FMap)
-- unquoteDecl H-Level-ISub = declare-record-hlevel 2 H-Level-ISub (quote ISub)

instance
  Funlike-FMap : Funlike ur (FMap A B) A (λ _ → Maybe B)
  Funlike-FMap ._#_ = fun

fmap-ext : ⦃ H-Level 2 B ⦄
         → {m₁ m₂ : FMap A B} → m₁ .fun ＝ m₂ .fun → m₁ .dom ＝ m₂ .dom → m₁ ＝ m₂
fmap-ext {m₁ = mkfmap f₁ d₁ c₁} {m₂ = mkfmap f₂ d₂ c₂} ef ed =
  ap² (mkfmap $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → ≃-is-of-hlevel 1 (hlevel 1) (hlevel 1)) _ c₂))

just-dom : ⦃ da : is-discrete A ⦄
         → {f : FMap A B} {a : A} {b : B}
         → (f $ a) ＝ just b → a ∈ f .dom
just-dom {f} e =
   dec→essentially-classical Dec-∈ₛ
   λ x → false! (e ⁻¹ ∙ (f .nde $ x))

dom-just : ⦃ da : is-discrete A ⦄
         → {f : FMap A B} {a : A}
         → a ∈ f .dom → Σ[ b ꞉ B ] ((f $ a) ＝ just b)
dom-just {f} {a} a∈ with f $ a | recall (f $_) a
... | just b  | _      = b , refl
... | nothing | ⟪ eq ⟫ = absurd ((f .nde ⁻¹ $ eq) a∈)

just-dom≃ : ⦃ da : is-discrete A ⦄
          → ⦃ H-Level 2 B ⦄
         → {f : FMap A B} {x : A}
         → (Σ[ b ꞉ B ] ((f $ x) ＝ just b)) ≃ x ∈ f .dom
just-dom≃ {f} =
  prop-extₑ
    (λ where
         (b1 , e1) (b2 , e2) →
            Σ-prop-path (λ x → hlevel 1)
                        (just-inj (e1 ⁻¹ ∙ e2)))
    (hlevel 1)
    (λ where (b , e) → just-dom {f = f} e)
    (dom-just {f = f})

emp : ⦃ H-Level 2 B ⦄
    → FMap A B
emp .fun _ = nothing
emp .dom = []
emp .nde = prop-extₑ! (λ _ → refl) (λ _ → ∉ₛ[])

cnst : ⦃ da : is-discrete A ⦄ → ⦃ H-Level 2 B ⦄
     → LFSet A → B → FMap A B
cnst d b .fun a   = if a ∈ₛ? d then just b else nothing
cnst d b .dom     = d
cnst d b .nde {x} =
  prop-extₑ!
    (λ x∉ → given-no x∉
              return (λ q → (if ⌊ q ⌋ then just b else nothing) ＝ nothing)
              then refl)
    (Dec.elim
      {C = λ q → (if ⌊ q ⌋ then just b else nothing) ＝ nothing → x ∉ d}
      (λ _ → false!)
      (λ x∉ _ → x∉)
      (x ∈? d))

_⊔[_]_ : ⦃ H-Level 2 B ⦄
       → FMap A B → (B → B → B) → FMap A B → FMap A B
(f1 ⊔[ g ] f2) .fun a = These.rec id id g <$> fromMaybe2 (f1 $ a) (f2 $ a)
(f1 ⊔[ g ] f2) .dom = f1 .dom ∪∷ f2 .dom
(f1 ⊔[ g ] f2) .nde =
  prop-extₑ!
    (λ x∉∪ →
      let (n1 , n2) = ∉ₛ-∪∷ x∉∪ in
      ap (mapₘ (These.rec id id g)) $
      ap² fromMaybe2 (f1 .nde $ n1) (f2 .nde $ n2))
    λ e →
      let (n1 , n2) = fromMaybe2-nothing (mapₘ=nothing e)
        in
      ∪∷-∉ₛ (f1 .nde ⁻¹ $ n1) (f2 .nde ⁻¹ $ n2)

_⊓[_]_ : ⦃ da : is-discrete A ⦄ → ⦃ H-Level 2 B ⦄
       → FMap A B → (B → B → B) → FMap A B → FMap A B
(f1 ⊓[ g ] f2) .fun a = fromMaybe2 (f1 $ a) (f2 $ a) >>= These.rec (λ _ → nothing) (λ _ → nothing) (λ x y → just $ g x y)
(f1 ⊓[ g ] f2) .dom = f1 .dom ∩∷ f2 .dom
(f1 ⊓[ g ] f2) .nde {x} =
  prop-extₑ!
    (λ x∉∩ →
        [ (λ where (x∉1 , x∈2) →
                      let e1 = f1 .nde $ x∉1
                          (b2 , e2) = dom-just {f = f2} x∈2
                        in
                      ap² (λ d e → fromMaybe2 d e >>= These.rec (λ _ → nothing) (λ _ → nothing) (λ x y → just $ g x y))
                          e1 e2)
        , [ (λ where (x∈1 , x∉2) →
                      let (b1 , e1) = dom-just {f = f1} x∈1
                          e2 = f2 .nde $ x∉2
                        in
                      ap² (λ d e → fromMaybe2 d e >>= These.rec (λ _ → nothing) (λ _ → nothing) (λ x y → just $ g x y))
                          e1 e2)
          , (λ where (x∉1 , x∉2) →
                      let e1 = f1 .nde $ x∉1
                          e2 = f2 .nde $ x∉2
                        in
                      ap² (λ d e → fromMaybe2 d e >>= These.rec (λ _ → nothing) (λ _ → nothing) (λ x y → just $ g x y))
                          e1 e2)
          ]ᵤ
        ]ᵤ (∉-∩∷ x∉∩))
    λ e →
        [ (λ e′ → let (n1 , n2) = fromMaybe2-nothing e′ in
                  ∩∷-∉-l (f1 .nde ⁻¹ $ n1))
        , (λ where
               (t , ej , ne) →
                  Maybe.elim
                    (λ q → (f1 $ x) ＝ q → fromMaybe2 q (f2 $ x) ＝ just t → x ∉ (f1 .dom ∩∷ f2 .dom))
                    (λ n1 _ → ∩∷-∉-l (f1 .nde ⁻¹ $ n1))
                    (λ b1 j1 →
                      Maybe.elim
                        (λ q → (f2 $ x) ＝ q → fromMaybe2 (just b1) q ＝ just t → x ∉ (f1 .dom ∩∷ f2 .dom))
                        (λ n2 _ → ∩∷-∉-r (f2 .nde ⁻¹ $ n2))
                        (λ b2 j2 e → false! (  ap (These.rec (λ _ → nothing) (λ _ → nothing)
                                                             (λ x y → just $ g x y))
                                                  (just-inj e)
                                             ∙ ne))
                        (f2 $ x) refl)
                    (f1 $ x) refl ej)
        ]ᵤ (bindₘ=nothing {m = fromMaybe2 (f1 $ x) (f2 $ x)} e)

