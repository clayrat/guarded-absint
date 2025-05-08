module SPA.FMap.Bounded.Order where

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
open import Order.Diagram.Meet
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Lattice

open import Order.Constructions.Maybe
open import Order.Constructions.Pointwise

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete
open import LFSet.Order

open import SPA.FMap
open import SPA.FMap.Bounded
open import SPA.FMap.Order

private variable
  ℓᵃ ℓᵇ ℓ : Level
  A : 𝒰 ℓᵃ
  bp : Poset ℓᵇ ℓ
  ks : LFSet A

open Displayed public

FMapBndₚ-over : (A : 𝒰 ℓᵃ)
              → ⦃ da : is-discrete A ⦄
              → (bp : Poset ℓᵇ ℓ)
              → Displayed (ℓᵃ ⊔ ℓᵇ) (ℓᵃ ⊔ ℓ) (LFSetₚ A)
FMapBndₚ-over A bp .Ob[_] = FMapBnd A (Poset.Ob bp)
FMapBndₚ-over A bp .Rel[_] _ f1 f2 = FMap≤ (bp .Poset._≤_) (f1 .fmap) (f2 .fmap)
FMapBndₚ-over A bp .≤-refl' {x'} = FMapₚ A bp .Poset.≤-refl {x = x' .fmap}
FMapBndₚ-over A bp .≤-thin' _ {x'} {y'} = FMapₚ A bp .Poset.≤-thin {x = x' .fmap} {y = y' .fmap}
FMapBndₚ-over A bp .≤-trans' {x'} {y'} {z'} = FMapₚ A bp .Poset.≤-trans {x = x' .fmap} {y = y' .fmap} {z = z' .fmap}
FMapBndₚ-over A bp .≤-antisym' xy yx = fmapbnd-ext (FMapₚ A bp .Poset.≤-antisym xy yx)

FMapBndₚ : (A : 𝒰 ℓᵃ)
         → ⦃ da : is-discrete A ⦄
         → Poset ℓᵇ ℓ
         → LFSet A
         → Poset (ℓᵃ ⊔ ℓᵇ) (ℓᵃ ⊔ ℓ)
FMapBndₚ A bp = Fibre (FMapBndₚ-over A bp)

instance
  FMapBnd-bottom : ⦃ da : is-discrete A ⦄
                 → Bottom (FMapBndₚ A bp ks)
  FMapBnd-bottom .Bottom.bot = empb
  FMapBnd-bottom .Bottom.bot-is-bot x = false! ⦃ Refl-x∉ₛ[] ⦄ , (λ a → lift tt)

  FMapBnd-top : ⦃ da : is-discrete A ⦄
              → ⦃ t : Top bp ⦄
              → Top (FMapBndₚ A bp ks)
  FMapBnd-top           ⦃ t ⦄ .Top.top          = cnstb (t .Top.top)
  FMapBnd-top {bp} {ks} ⦃ t ⦄ .Top.top-is-top x =
      (x .bnd)
    , (λ a → Maybe.elim
              (λ q → x # a ＝ q → Maybe≤ (Poset._≤_ bp) q
                                   (if a ∈ₛ? ks then just (t .Top.top) else nothing))
              (λ _ → lift tt)
              (λ b e → given-yes (x .bnd (just-dom {f = x .fmap} e))
                          return (λ q → Maybe≤ (Poset._≤_ bp)
                                          (just b)
                                          (if ⌊ q ⌋ then just (t .Top.top) else nothing))
                          then t .Top.top-is-top b)
              (x $ a)
              refl)
