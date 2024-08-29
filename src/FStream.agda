module FStream where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Maybe
open import Data.Nat renaming (_==_ to _==ⁿ_)
open import Data.Nat.Order.Base
  renaming ( _≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_
           ; ≤-refl to ≤ⁿ-refl ; ≤-trans to ≤ⁿ-trans ; ≤-antisym to ≤ⁿ-antisym)
open import Data.Nat.Order.Inductive.Base using (_≤?_)
open import Data.Reflects

open import Order.Base
open import Order.SupLattice
open import Order.SupLattice.SmallBasis
open import Order.SupLattice.SmallBasis.Closure

module _ {ℓ} where

  FStream : 𝒰 ℓ → 𝒰 ℓ
  FStream A = ℕ → A

  shl : {A : 𝒰 ℓ} → (ℕ → A) → ℕ → ℕ → A
  shl f n k = f (k + n)

module _ {ℓ} {A : 𝒰 ℓ} where

  null : FStream (Maybe A)
  null _ = nothing

  single-at : A → ℕ → FStream (Maybe A)
  single-at a n k = if n =? k then just a else nothing

  shr : FStream (Maybe A) → ℕ → ℕ → Maybe A
  shr f n k = if n ≤? k then f (k ∸ n) else nothing

  filt : FStream (Maybe A) → (ℕ → Bool) → ℕ → Maybe A
  filt f p n = if p n then f n else nothing

  shl-single-at-not : {b : A} {n m : ℕ}
                    → n <ⁿ m
                    → shl (single-at b n) m ＝ null
  shl-single-at-not {n} {m} lt =
    fun-ext λ k → if-false (false→so! ⦃ Reflects-ℕ-Path ⦄
                                      (contra (λ e → subst (m ≤ⁿ_) (e ⁻¹) (≤-+-l))
                                              (<→≱ $ lt)))

  shl-shr : {f : FStream (Maybe A)} {n : ℕ}
          → shl (shr f n) n ＝ f
  shl-shr {f} {n} = fun-ext λ k → if-true (true→so! (≤-+-l {m = n}))
                                            ∙ ap f (+-cancel-∸-r k n)

  shl-filt-not : {f : FStream (Maybe A)} {p : ℕ → Bool} {n : ℕ}
               → (∀ m → n ≤ⁿ m → ⌞ not (p m) ⌟)
               → shl (filt f p) n ＝ null
  shl-filt-not {n} h = fun-ext λ k → if-false (h (k + n) ≤-+-l)

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         {P : Poset o ℓ}
         {L : is-sup-lattice P ℓ′}
         {β : B → ⌞ P ⌟}
         where

  fstream-at-basis : ∀ n → is-basis P L β → is-basis {B = ℕ → B} P L (λ f → β (f n))
  fstream-at-basis n = cover-preserves-basis ((_$ n) , λ b → ∣ (λ _ → b) , refl ∣₁)

module _ {o ℓ ℓ′} {B : 𝒰 ℓ′}
         {P : Poset o ℓ}
         {L : is-sup-lattice P ℓ′}
         {β : (ℕ → Maybe B) → ⌞ P ⌟}
         where

  fstream-shl-basis : ∀ k → is-basis {B = ℕ → Maybe B} P L β → is-basis {B = ℕ → Maybe B} P L (λ f → β (shl f k))
  fstream-shl-basis k = cover-preserves-basis ((λ f → shl f k) , λ f → ∣ (shr f k) , shl-shr {n = k} ∣₁)
