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
FMap≤ {A} le f1 f2 = (a : A) → Maybe≤ le (f1 $ a) (f2 $ a)

FMap≤-dom : ∀ {ℓ} {A : 𝒰 ℓᵃ} ⦃ da : is-discrete A ⦄
          → {le : B → B → 𝒰 ℓ} {f1 f2 : FMap A B}
          → FMap≤ le f1 f2 → f1 .dom ⊆ f2 .dom
FMap≤-dom {le} {f1} {f2} fle {x} x∈f1 =
  let (b1 , e1) = dom-just {f = f1} x∈f1
      (y , me , le) = Maybe≤-just-l {my = f2 $ x} (subst (λ q → Maybe≤ le q (f2 $ x)) e1 (fle x))
    in
  just-dom {f = f2} me

FMapₚ : ∀ {ℓ ℓᵇ} (A : 𝒰 ℓᵃ) → ⦃ is-discrete A ⦄
      → Poset ℓᵇ ℓ → Poset (ℓᵃ ⊔ ℓᵇ) (ℓᵃ ⊔ ℓ)
FMapₚ A bp .Poset.Ob = FMap A (Poset.Ob bp)
FMapₚ _ bp .Poset._≤_ = FMap≤ (bp .Poset._≤_)
FMapₚ _ bp .Poset.≤-thin {x} =
  Π-is-of-hlevel 1 λ a → (Maybeₚ bp).Poset.≤-thin {x = x $ a}
FMapₚ _ bp .Poset.≤-refl {x} a =
  (Maybeₚ bp).Poset.≤-refl {x = x $ a}
FMapₚ _ bp .Poset.≤-trans {x} xy yz a =
  (Maybeₚ bp).Poset.≤-trans {x = x $ a} (xy a) (yz a)
FMapₚ _ bp .Poset.≤-antisym {x} {y} xy yx =
  fmap-ext
    (fun-ext λ a → (Maybeₚ bp).Poset.≤-antisym (xy a) (yx a))
    (set-ext λ z → prop-extₑ! (FMap≤-dom {f1 = x} {f2 = y} xy)
                              (FMap≤-dom {f1 = y} {f2 = x} yx))

-- join

l≤⊔f : ⦃ da : is-discrete A ⦄
     → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄ → (open JR bp hj)
     → {x y : FMap A (Poset.Ob bp)}
     → (FMapₚ A bp).Poset._≤_ x (x ⊔[ _∪_ ] y)
l≤⊔f {bp} ⦃ hj ⦄ {x} {y} a =
  Maybe.elim
    (λ q → Maybe≤ (Poset._≤_ bp) q (mapₘ (These.rec id id _∪_) (These.fromMaybe2 q (y $ a))))
    (lift tt)
    (λ b₁ → Maybe.elim
              (λ q → Maybe≤ (Poset._≤_ bp) (just b₁) (mapₘ (These.rec id id _∪_) (fromMaybe2 (just b₁) q)))
              (Poset.≤-refl bp)
              (λ b₂ → l≤∪′)
              (y $ a))
    (x $ a)
  where
    open JR bp hj public renaming (l≤∪ to l≤∪′)

r≤⊔f : ⦃ da : is-discrete A ⦄
     → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄ → (open JR bp hj)
     → {x y : FMap A (Poset.Ob bp)}
     → (FMapₚ A bp).Poset._≤_ y (x ⊔[ _∪_ ] y)
r≤⊔f {bp} ⦃ hj ⦄ {x} {y} a =
  Maybe.elim
    (λ q → Maybe≤ (Poset._≤_ bp) q (mapₘ (These.rec id id _∪_) (These.fromMaybe2 (x $ a) q)))
    (lift tt)
    (λ b₂ → Maybe.elim
              (λ q → Maybe≤ (Poset._≤_ bp) (just b₂) (mapₘ (These.rec id id _∪_) (fromMaybe2 q (just b₂))))
              (Poset.≤-refl bp)
              (λ b₁ → r≤∪′)
              (x $ a))
    (y $ a)
  where
    open JR bp hj public renaming (r≤∪ to r≤∪′)

⊔f≤ : ⦃ da : is-discrete A ⦄
    → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄ → (open JR bp hj)
    → {x y : FMap A (Poset.Ob bp)}
    → (z : FMap A (Poset.Ob bp))
    → (FMapₚ A bp).Poset._≤_ x z
    → (FMapₚ A bp).Poset._≤_ y z
    → (FMapₚ A bp).Poset._≤_ (x ⊔[ _∪_ ] y) z
⊔f≤ {bp} ⦃ hj ⦄ {x} {y} z xz yz a =
  Maybe.elim
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
              (y $ a) (yz a))
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
              (y $ a) (yz a))
    (x $ a) (xz a)
  where
    open JR bp hj public renaming (∪-universal to ∪-universal′)

-- meet

⊓f≤l : ⦃ da : is-discrete A ⦄
     → {bp : Poset ℓᵇ ℓ} → ⦃ hm : Has-meets bp ⦄ → (open MR bp hm)
     → {x y : FMap A (Poset.Ob bp)}
     → (FMapₚ A bp).Poset._≤_ (x ⊓[ _∩_ ] y) x
⊓f≤l {bp} ⦃ hm ⦄ {x} {y} a =
  Maybe.elim
    (λ q → Maybe≤ (Poset._≤_ bp)
         (bindₘ (fromMaybe2 q (y $ a))
                (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b))))
         q)
    (Maybe.elim
       (λ q → Maybe≤ (Poset._≤_ bp)
                     (bindₘ (fromMaybe2 nothing q)
                            (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b))))
                     nothing)
       (lift tt)
       (λ m → lift tt)
       (y $ a))
    (λ n →
       Maybe.elim
       (λ q → Maybe≤ (Poset._≤_ bp)
                     (bindₘ (fromMaybe2 (just n) q)
                            (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b))))
                     (just n))
       (lift tt)
       (λ m → ∩≤l′)
       (y $ a))
    (x $ a)
  where
    open MR bp hm public renaming (∩≤l to ∩≤l′)

⊓f≤r : ⦃ da : is-discrete A ⦄
     → {bp : Poset ℓᵇ ℓ} → ⦃ hm : Has-meets bp ⦄ → (open MR bp hm)
     → {x y : FMap A (Poset.Ob bp)}
     → (FMapₚ A bp).Poset._≤_ (x ⊓[ _∩_ ] y) y
⊓f≤r {bp} ⦃ hm ⦄ {x} {y} a =
  Maybe.elim
    (λ q → Maybe≤ (Poset._≤_ bp)
                  (bindₘ (fromMaybe2 q (y $ a))
                         (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b))))
                  (y $ a))
    (Maybe.elim
       (λ q → Maybe≤ (Poset._≤_ bp)
                     (bindₘ (fromMaybe2 nothing q)
                            (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b))))
                     q)
       (lift tt)
       (λ m → lift tt)
       (y $ a))
    (λ n →
       Maybe.elim
       (λ q → Maybe≤ (Poset._≤_ bp)
                     (bindₘ (fromMaybe2 (just n) q)
                            (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b))))
                     q)
       (lift tt)
       (λ m → ∩≤r′)
       (y $ a))
    (x $ a)
  where
    open MR bp hm public renaming (∩≤r to ∩≤r′)

≤⊓f : ⦃ da : is-discrete A ⦄
    → {bp : Poset ℓᵇ ℓ} → ⦃ hm : Has-meets bp ⦄ → (open MR bp hm)
    → {x y : FMap A (Poset.Ob bp)}
    → (z : FMap A (Poset.Ob bp))
    → (FMapₚ A bp).Poset._≤_ z x
    → (FMapₚ A bp).Poset._≤_ z y
    → (FMapₚ A bp).Poset._≤_ z (x ⊓[ _∩_ ] y)
≤⊓f {bp} ⦃ hm ⦄ {x} {y} z zx zy a =
  Maybe.elim
    (λ q → Maybe≤ (Poset._≤_ bp)
                  (z $ a) q
         → Maybe≤ (Poset._≤_ bp)
                  (z $ a)
                  (bindₘ (fromMaybe2 q (y $ a))
                         (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b)))))
    (λ mx → Maybe.elim
              (λ q → Maybe≤ (Poset._≤_ bp)
                            (z $ a) q
                   → Maybe≤ (Poset._≤_ bp)
                            (z $ a)
                            (bindₘ (fromMaybe2 nothing q)
                                   (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b)))))
              (λ _ → mx)
              (λ _ _ → mx)
              (y $ a) (zy a))
    (λ b₁ mx → Maybe.elim
                (λ q → Maybe≤ (Poset._≤_ bp)
                              (z $ a) q
                     → Maybe≤ (Poset._≤_ bp)
                              (z $ a)
                              (bindₘ (fromMaybe2 (just b₁) q)
                                     (These.rec (λ _ → nothing) (λ _ → nothing) (λ a b → just (a ∩ b)))))
              (λ my → my)
              (λ b₂ my → Maybe.elim
                            (λ q → Maybe≤ (Poset._≤_ bp) q (just b₁)
                                 → Maybe≤ (Poset._≤_ bp) q (just b₂)
                                 → Maybe≤ (Poset._≤_ bp) q (just (b₁ ∩ b₂)))
                            (λ _ → id)
                            ∩-universal′
                            (z $ a) mx my)
              (y $ a) (zy a))
    (x $ a) (zx a)
  where
    open MR bp hm public renaming (∩-universal to ∩-universal′)

-- instances

instance
  FMap-bottom : ∀ {ℓ ℓᵇ} {A : 𝒰 ℓᵃ} → ⦃ da : is-discrete A ⦄
              → {bp : Poset ℓᵇ ℓ} → Bottom (FMapₚ A bp)
  FMap-bottom .Bottom.bot = emp
  FMap-bottom .Bottom.bot-is-bot x a = lift tt

  FMap-joins : ∀ {ℓ ℓᵇ} {A : 𝒰 ℓᵃ} → ⦃ da : is-discrete A ⦄
             → {bp : Poset ℓᵇ ℓ} → ⦃ hj : Has-joins bp ⦄
             → Has-joins (FMapₚ A bp)
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.lub = x ⊔[ _∪_ ] y
    where
      open JR bp hj public
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.l≤join = l≤⊔f {bp = bp} {x = x} {y = y}
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.r≤join = r≤⊔f {bp = bp} {x = x} {y = y}
  FMap-joins {bp} ⦃ hj ⦄ {x} {y} .Join.has-join .is-join.least = ⊔f≤ {bp = bp} {x = x} {y = y}

  FMap-meets : ∀ {ℓ ℓᵇ} {A : 𝒰 ℓᵃ} → ⦃ da : is-discrete A ⦄
             → {bp : Poset ℓᵇ ℓ} → ⦃ hm : Has-meets bp ⦄
             → Has-meets (FMapₚ A bp)
  FMap-meets {bp} ⦃ hm ⦄ {x} {y} .Meet.glb = x ⊓[ _∩_ ] y
    where
      open MR bp hm public
  FMap-meets {bp} ⦃ (hm) ⦄ {x} {y} .Meet.has-meet .is-meet.meet≤l = ⊓f≤l {bp = bp} {x = x} {y = y}
  FMap-meets {bp} ⦃ (hm) ⦄ {x} {y} .Meet.has-meet .is-meet.meet≤r = ⊓f≤r {bp = bp} {x = x} {y = y}
  FMap-meets {bp} ⦃ (hm) ⦄ {x} {y} .Meet.has-meet .is-meet.greatest = ≤⊓f {bp = bp} {x = x} {y = y}


{-
-- strict

FMap< : ∀ {ℓ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
      → (B → B → 𝒰 ℓ)
      → FMap A B → FMap A B → 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ)
FMap< {A} le f1 f2 = (FMap≤ le f1 f2) × (f1 ≠ f2)

FMap<-wf : ∀ {ℓ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
         → {le : B → B → 𝒰 ℓ} → is-wf (λ x y → (le x y) × (x ≠ y))
         → is-wf (FMap< {A = A} le)
FMap<-wf wle x = acc λ y y<x → {!!}
-}
