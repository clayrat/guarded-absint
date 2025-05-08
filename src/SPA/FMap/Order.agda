module SPA.FMap.Order where

open import Prelude
open import Data.Empty hiding (_≠_)
open import Data.Unit
open import Data.Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base renaming (_≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_)
open import Data.Maybe as Maybe
open import Data.These as These
open import Data.Sum
open import Data.Acc

open import Order.Base
open import Order.Displayed

open import Order.Diagram.Bottom
open import Order.Diagram.Top
open import Order.Diagram.Join
open import Order.Diagram.Join.Reasoning as JR
open import Order.Diagram.Meet
open import Order.Diagram.Meet.Reasoning as MR
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Lattice

open import Order.Constructions.Maybe
open import Order.Constructions.Pointwise

open import SPA.FMap
open import LFSet
open import LFSet.Membership
open import LFSet.Discrete
open import LFSet.Order

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ

FMap≤ : ∀ {ℓ} {A : 𝒰 ℓᵃ}
      → (B → B → 𝒰 ℓ)
      → FMap A B → FMap A B → 𝒰 (ℓᵃ ⊔ ℓ)
FMap≤ {A} le f1 f2 = (f1 .dom ⊆ f2 .dom) × ((a : A) → Maybe≤ le (f1 $ a) (f2 $ a))

FMapₚ : ∀ {ℓ ℓᵇ} (A : 𝒰 ℓᵃ) → ⦃ is-discrete A ⦄
      → Poset ℓᵇ ℓ → Poset (ℓᵃ ⊔ ℓᵇ) (ℓᵃ ⊔ ℓ)
FMapₚ A bp .Poset.Ob = FMap A (Poset.Ob bp)
FMapₚ _ bp .Poset._≤_ = FMap≤ (bp .Poset._≤_)
FMapₚ _ bp .Poset.≤-thin {x} =
  ×-is-of-hlevel 1
    hlevel!
    (Π-is-of-hlevel 1 λ a → (Maybeₚ bp).Poset.≤-thin {x = x $ a})
FMapₚ _ bp .Poset.≤-refl {x} =
    id
  , λ a → (Maybeₚ bp).Poset.≤-refl {x = x $ a}
FMapₚ _ bp .Poset.≤-trans {x} (xyd , xyf) (yzd , yzf) =
    yzd ∘ xyd
  , λ a → (Maybeₚ bp).Poset.≤-trans {x = x $ a} (xyf a) (yzf a)
FMapₚ _ bp .Poset.≤-antisym {x} (xyd , xyf) (yxd , yxf) =
  fmap-ext
    (fun-ext λ a → (Maybeₚ bp).Poset.≤-antisym (xyf a) (yxf a))
    (set-ext λ z → prop-extₑ! xyd yxd)

l≤⊔f : ⦃ da : is-discrete A ⦄
     → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄ → (open JR bp hj)
     → {x y : FMap A (Poset.Ob bp)}
     → (FMapₚ A bp).Poset._≤_ x (x ⊔[ _∪_ ] y)
l≤⊔f {bp} ⦃ hj ⦄ {x} {y} =
    ∈ₛ-∪∷←l
  , (λ a → Maybe.elim
             (λ q → Maybe≤ (Poset._≤_ bp) q (mapₘ (These.rec id id _∪_) (These.fromMaybe2 q (y $ a))))
             (lift tt)
             (λ b₁ → Maybe.elim
                       (λ q → Maybe≤ (Poset._≤_ bp) (just b₁) (mapₘ (These.rec id id _∪_) (fromMaybe2 (just b₁) q)))
                       (Poset.≤-refl bp)
                       (λ b₂ → l≤∪′)
                       (y $ a))
             (x $ a))
  where
    open JR bp hj public renaming (l≤∪ to l≤∪′)

r≤⊔f : ⦃ da : is-discrete A ⦄
     → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄ → (open JR bp hj)
     → {x y : FMap A (Poset.Ob bp)}
     → (FMapₚ A bp).Poset._≤_ y (x ⊔[ _∪_ ] y)
r≤⊔f {bp} ⦃ hj ⦄ {x} {y} =
    ∈ₛ-∪∷←r {s₁ = x .dom}
  , (λ a → Maybe.elim
             (λ q → Maybe≤ (Poset._≤_ bp) q (mapₘ (These.rec id id _∪_) (These.fromMaybe2 (x $ a) q)))
             (lift tt)
             (λ b₂ → Maybe.elim
                       (λ q → Maybe≤ (Poset._≤_ bp) (just b₂) (mapₘ (These.rec id id _∪_) (fromMaybe2 q (just b₂))))
                       (Poset.≤-refl bp)
                       (λ b₁ → r≤∪′)
                       (x $ a))
             (y $ a))
  where
    open JR bp hj public renaming (r≤∪ to r≤∪′)

⊔f≤ : ⦃ da : is-discrete A ⦄
    → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄ → (open JR bp hj)
    → {x y : FMap A (Poset.Ob bp)}
    → (z : FMap A (Poset.Ob bp))
    → (FMapₚ A bp).Poset._≤_ x z
    → (FMapₚ A bp).Poset._≤_ y z
    → (FMapₚ A bp).Poset._≤_ (x ⊔[ _∪_ ] y) z
⊔f≤ {bp} ⦃ hj ⦄ {x} {y} z (xzd , xzf) (yzd , yzf) =
    [ xzd , yzd ]ᵤ ∘ ∈ₛ-∪∷→
  , λ a → Maybe.elim
             (λ q → Maybe≤ (Poset._≤_ bp)
                           q (z $ a)
                  → Maybe≤ (Poset._≤_ bp)
                           (mapₘ (These.rec id id _∪_) (These.fromMaybe2 q (y $ a)))
                           (z $ a))
             (λ mx → Maybe.elim
                       (λ q → Maybe≤ (Poset._≤_ bp)
                                     q (z $ a)
                            → Maybe≤ (Poset._≤_ bp)
                                     (mapₘ (These.rec id id _∪_) (fromMaybe2 nothing q))
                                     (z $ a))
                       (λ _ → lift tt)
                       (λ b₂ my → my)
                       (y $ a) (yzf a))
             (λ b₁ mx → Maybe.elim
                         (λ q → Maybe≤ (Poset._≤_ bp)
                                     q (z $ a)
                              → Maybe≤ (Poset._≤_ bp)
                                       (mapₘ (These.rec id id _∪_) (fromMaybe2 (just b₁) q))
                                       (z $ a))
                       (λ _ → mx)
                       (λ b₂ my → Maybe.elim
                                     (λ q → Maybe≤ (Poset._≤_ bp) (just b₁) q
                                          → Maybe≤ (Poset._≤_ bp) (just b₂) q
                                          → Maybe≤ (Poset._≤_ bp) (just (b₁ ∪ b₂)) q)
                                     (λ _ → id)
                                     ∪-universal′
                                     (z $ a) mx my)
                       (y $ a) (yzf a))
             (x $ a) (xzf a)
  where
    open JR bp hj public renaming (∪-universal to ∪-universal′)

instance
  FMap-bottom : ∀ {ℓ ℓᵇ} {A : 𝒰 ℓᵃ} → ⦃ da : is-discrete A ⦄
              → {bp : Poset ℓᵇ ℓ} → Bottom (FMapₚ A bp)
  FMap-bottom .Bottom.bot = emp
  FMap-bottom .Bottom.bot-is-bot x = false! ⦃ Refl-x∉ₛ[] ⦄ , (λ a → lift tt)

  FMap-joins : ∀ {ℓ ℓᵇ} {A : 𝒰 ℓᵃ} → ⦃ da : is-discrete A ⦄
             → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄
             → Has-joins (FMapₚ A bp)
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.lub = x ⊔[ _∪_ ] y
    where
      open JR bp hj public
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.l≤join = l≤⊔f {bp = bp} {x = x} {y = y}
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.r≤join = r≤⊔f {bp = bp} {x = x} {y = y}
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.least = ⊔f≤ {bp = bp} {x = x} {y = y}
