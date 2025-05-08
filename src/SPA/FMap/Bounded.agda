{-# OPTIONS --safe #-}
module SPA.FMap.Bounded where

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

open import SPA.FMap

-- cofinitely quantified finite key-bounded maps
-- (dom overapproximates the actual domain)
-- TODO should probably do an equivalence instead of cofinite implication

private variable
  ℓᵃ ℓᵇ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  ks : LFSet A

record FMapBnd (A : 𝒰 ℓᵃ) (B : 𝒰 ℓᵇ) (keys : LFSet A) : 𝒰 (ℓᵃ ⊔ ℓᵇ) where
  constructor mkfmapbnd
  field
    fmap : FMap A B
    bnd  : fmap .dom ⊆ keys

open FMapBnd public

unquoteDecl FMapBnd-Iso = declare-record-iso FMapBnd-Iso (quote FMapBnd)

instance
  Funlike-FMapBnd : Funlike ur (FMapBnd A B ks) A (λ _ → Maybe B)
  Funlike-FMapBnd ._#_ f x = f .fmap # x

fmapbnd-ext : ⦃ H-Level 2 B ⦄ → {m₁ m₂ : FMapBnd A B ks} → m₁ .fmap ＝ m₂ .fmap → m₁ ＝ m₂
fmapbnd-ext {m₁ = mkfmapbnd f₁ b₁} {m₂ = mkfmapbnd f₂ b₂} ef =
  ap² mkfmapbnd ef (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∈ → hlevel 1) _ b₂))

empb : FMapBnd A B ks
empb .fmap = emp
empb .bnd = false! ⦃ Refl-x∉ₛ[] ⦄

cnstb : ⦃ da : is-discrete A ⦄ → B → FMapBnd A B ks
cnstb {ks} b .fmap = cnst ks b
cnstb      b .bnd  = id

_⊔[_]b_ : ⦃ da : is-discrete A ⦄
        → FMapBnd A B ks → (B → B → B) → FMapBnd A B ks → FMapBnd A B ks
(f1 ⊔[ g ]b f2) .fmap = f1 .fmap ⊔[ g ] f2 .fmap
(f1 ⊔[ g ]b f2) .bnd = [ f1 .bnd , f2 .bnd ]ᵤ ∘ ∈ₛ-∪∷→

_⊓[_]b_ : ⦃ da : is-discrete A ⦄
        → FMapBnd A B ks → (B → B → B) → FMapBnd A B ks → FMapBnd A B ks
(f1 ⊓[ g ]b f2) .fmap = f1 .fmap ⊓[ g ] f2 .fmap
(f1 ⊓[ g ]b f2) .bnd = f1 .bnd ∘ fst ∘ ∩∷-∈
