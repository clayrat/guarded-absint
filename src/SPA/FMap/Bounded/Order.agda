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
open import Order.Diagram.Join.Reasoning as JR
open import Order.Diagram.Meet
open import Order.Diagram.Meet.Reasoning as MR
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

  FMapBnd-joins : ⦃ da : is-discrete A ⦄
                → ⦃ hj : Has-joins bp ⦄
                → Has-joins (FMapBndₚ A bp ks)
  FMapBnd-joins {bp} ⦃ hj ⦄ {x} {y} .Join.lub = x ⊔[ _∪_ ]b y
    where
      open JR bp hj public
  FMapBnd-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.l≤join =
    l≤⊔f {bp = bp} {x = x .fmap} {y = y .fmap}
  FMapBnd-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.r≤join =
    r≤⊔f {bp = bp} {x = x .fmap} {y = y .fmap}
  FMapBnd-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.least ub =
    ⊔f≤ {bp = bp} {x = x .fmap} {y = y .fmap} (ub .fmap)

  FMapBnd-meets : ⦃ da : is-discrete A ⦄
                → ⦃ hm : Has-meets bp ⦄
                → Has-meets (FMapBndₚ A bp ks)
  FMapBnd-meets {bp} ⦃ hm ⦄ {x} {y} .Meet.glb = x ⊓[ _∩_ ]b y
    where
      open MR bp hm public
  FMapBnd-meets {bp} ⦃ (hm) ⦄ {x} {y} .Meet.has-meet .is-meet.meet≤l =
    ⊓f≤l {bp = bp} {x = x .fmap} {y = y .fmap}
  FMapBnd-meets {bp} ⦃ (hm) ⦄ {x} {y} .Meet.has-meet .is-meet.meet≤r =
    ⊓f≤r {bp = bp} {x = x .fmap} {y = y .fmap}
  FMapBnd-meets {bp} ⦃ (hm) ⦄ {x} {y} .Meet.has-meet .is-meet.greatest ub =
    ≤⊓f {bp = bp} {x = x .fmap} {y = y .fmap} (ub .fmap)

  FMapBnd-join-slat : ⦃ da : is-discrete A ⦄
                    → ⦃ hj : Has-joins bp ⦄
                    → is-join-semilattice (FMapBndₚ A bp ks)
  FMapBnd-join-slat .is-join-semilattice.has-bottom = FMapBnd-bottom
  FMapBnd-join-slat .is-join-semilattice.has-joins  = FMapBnd-joins

  FMapBnd-meet-slat : ⦃ da : is-discrete A ⦄
                    → ⦃ ms : is-meet-semilattice bp ⦄
                    → is-meet-semilattice (FMapBndₚ A bp ks)
  FMapBnd-meet-slat ⦃ ms ⦄ .is-meet-semilattice.has-top   =
    FMapBnd-top ⦃ t = ms .is-meet-semilattice.has-top ⦄
  FMapBnd-meet-slat ⦃ ms ⦄ .is-meet-semilattice.has-meets =
    FMapBnd-meets ⦃ hm = ms .is-meet-semilattice.has-meets ⦄

  FMapBnd-lat : ⦃ da : is-discrete A ⦄
              → ⦃ la : is-lattice bp ⦄ -- can be split into has-joins + is-meet-semilattice
              → is-lattice (FMapBndₚ A bp ks)
  FMapBnd-lat ⦃ la ⦄ .is-lattice.has-join-slat =
    FMapBnd-join-slat ⦃ hj = la .is-lattice.has-join-slat .is-join-semilattice.has-joins ⦄
  FMapBnd-lat ⦃ la ⦄ .is-lattice.has-meet-slat =
    FMapBnd-meet-slat ⦃ ms = la .is-lattice.has-meet-slat ⦄
