{-# OPTIONS --safe #-}
module SPA.FMapC where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.Sum as Sum
open import Data.These as These

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

-- cofinitely quantified finite maps
-- (dom overapproximates the actual domain)

private variable
  ℓᵃ ℓᵇ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

record FMap (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) : 𝒰 (ℓᵃ ⊔ ℓᵇ) where
  constructor mkfmap
  field
    fun : A → Maybe B
    dom : LFSet A
    cof : ∀ {x} → x ∉ dom → fun x ＝ nothing

open FMap public

unquoteDecl FMap-Iso = declare-record-iso FMap-Iso (quote FMap)
-- unquoteDecl H-Level-ISub = declare-record-hlevel 2 H-Level-ISub (quote ISub)

instance
  Funlike-FMap : Funlike ur (FMap A B) A (λ _ → Maybe B)
  Funlike-FMap ._#_ = fun

fmap-ext : ⦃ H-Level 2 B ⦄ → {m₁ m₂ : FMap A B} → m₁ .fun ＝ m₂ .fun → m₁ .dom ＝ m₂ .dom → m₁ ＝ m₂
fmap-ext {m₁ = mkfmap f₁ d₁ c₁} {m₂ = mkfmap f₂ d₂ c₂} ef ed =
  ap² (mkfmap $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

just-dom : ⦃ da : is-discrete A ⦄ → {f : FMap A B} {a : A} {b : B}
         → (f $ a) ＝ just b → a ∈ f .dom
just-dom {f} e =
   dec→essentially-classical Dec-∈ₛ
   λ x → false! (e ⁻¹ ∙ f .cof x)

emp : FMap A B
emp .fun _ = nothing
emp .dom = []
emp .cof _ = refl

cnst : ⦃ da : is-discrete A ⦄ → LFSet A → B → FMap A B
cnst d b .fun a  = if a ∈ₛ? d then just b else nothing
cnst d b .dom    = d
cnst d b .cof x∉ =
  given-no x∉
      return (λ q → (if ⌊ q ⌋ then just b else nothing) ＝ nothing)
      then refl

_⊔[_]_ : FMap A B → (B → B → B) → FMap A B → FMap A B
(f1 ⊔[ g ] f2) .fun a = These.rec id id g <$> fromMaybe2 (f1 $ a) (f2 $ a)
(f1 ⊔[ g ] f2) .dom = f1 .dom ∪∷ f2 .dom
(f1 ⊔[ g ] f2) .cof x∉∪ =
  let (n1 , n2) = ∉ₛ-∪∷ x∉∪ in
  ap (mapₘ (These.rec id id g)) $
  ap² fromMaybe2 (f1 .cof n1) (f2 .cof n2)

_⊓[_]_ : ⦃ da : is-discrete A ⦄ → FMap A B → (B → B → B) → FMap A B → FMap A B
(f1 ⊓[ g ] f2) .fun a = fromMaybe2 (f1 $ a) (f2 $ a) >>= These.rec (λ _ → nothing) (λ _ → nothing) (λ x y → just $ g x y)
(f1 ⊓[ g ] f2) .dom = f1 .dom ∩∷ f2 .dom
(f1 ⊓[ g ] f2) .cof {x} x∉∩ with (f1 $ x) | recall (f1 $_) x | (f2 $ x) | recall (f2 $_) x
... | just b₁ | ⟪ eq1 ⟫ | just b₂ | ⟪ eq2 ⟫ = absurd (x∉∩ (∈-∩∷← (just-dom {f = f1} eq1) (just-dom {f = f2} eq2)))
... | just b₁ | _       | nothing | eq2 = refl
... | nothing | _       | just b₁ | eq2 = refl
... | nothing | _       | nothing | eq2 = refl
