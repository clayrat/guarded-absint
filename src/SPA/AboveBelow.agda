module SPA.AboveBelow where

open import Prelude
open import Data.Empty hiding (_≠_)
open import Data.Unit
open import Data.Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base renaming (_≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_)
open import Data.Maybe
open import Data.Sum
open import Data.Acc

open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Top
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Lattice

private variable
  ℓ : Level
  A : 𝒰 ℓ

data AboveBelow (A : 𝒰 ℓ) : 𝒰 ℓ where
  bt : AboveBelow A
  tp : AboveBelow A
  wr : A → AboveBelow A

unwr : AboveBelow A → Maybe A
unwr  bt    = nothing
unwr  tp    = nothing
unwr (wr x) = just x

is-bt : AboveBelow A → 𝒰
is-bt  bt    = ⊤
is-bt  tp    = ⊥
is-bt (wr _) = ⊥

is-tp : AboveBelow A → 𝒰
is-tp  bt    = ⊥
is-tp  tp    = ⊤
is-tp (wr _) = ⊥

bt≠tp : the (AboveBelow A) bt ≠ tp
bt≠tp e = subst is-bt e tt

bt≠wr : {a : A} → bt ≠ wr a
bt≠wr e = subst is-bt e tt

tp≠wr : {a : A} → tp ≠ wr a
tp≠wr e = subst is-tp e tt

wr-inj : {x y : A} → wr x ＝ wr y → x ＝ y
wr-inj = just-inj ∘ ap unwr

instance
  Discrete-AboveBelow : ⦃ da : is-discrete A ⦄ → is-discrete (AboveBelow A)
  Discrete-AboveBelow        {x = bt}   {y = bt}   = yes refl
  Discrete-AboveBelow        {x = bt}   {y = tp}   = no bt≠tp
  Discrete-AboveBelow        {x = bt}   {y = wr x} = no bt≠wr
  Discrete-AboveBelow        {x = tp}   {y = bt}   = no (bt≠tp ∘ _⁻¹)
  Discrete-AboveBelow        {x = tp}   {y = tp}   = yes refl
  Discrete-AboveBelow        {x = tp}   {y = wr x} = no tp≠wr
  Discrete-AboveBelow        {x = wr x} {y = bt}   = no (bt≠wr ∘ _⁻¹)
  Discrete-AboveBelow        {x = wr x} {y = tp}   = no (tp≠wr ∘ _⁻¹)
  Discrete-AboveBelow ⦃ da ⦄ {x = wr x} {y = wr y} = Dec.dmap (ap wr) (contra wr-inj) (da {x = x} {y = y})

-- preorder

data _AB≤_ {A : 𝒰 ℓ} : AboveBelow A → AboveBelow A → 𝒰 ℓ where
  bt≤   : {y : AboveBelow A} → bt AB≤ y
  wr≤wr : {x y : A} → x ＝ y → wr x AB≤ wr y
  wr≤tp : {x : A} → wr x AB≤ tp
  tp≤tp : tp AB≤ tp

≤tp : {x : AboveBelow A} → x AB≤ tp
≤tp {x = bt}   = bt≤
≤tp {x = tp}   = tp≤tp
≤tp {x = wr x} = wr≤tp

AB≤-prop : {sa : is-set A} → {x y : AboveBelow A} → is-prop (x AB≤ y)
AB≤-prop       bt≤        bt≤       = refl
AB≤-prop {sa} (wr≤wr e₁) (wr≤wr e₂) = ap wr≤wr (sa _ _ e₁ e₂)
AB≤-prop       wr≤tp      wr≤tp     = refl
AB≤-prop       tp≤tp      tp≤tp     = refl

-- TODO generalize?
instance opaque
  H-Level-AB≤ : ⦃ as : H-Level 2 A ⦄ → {x y : AboveBelow A} → H-Level 1 (x AB≤ y)
  H-Level-AB≤ = hlevel-prop-instance (AB≤-prop {sa = hlevel 2})
  {-# OVERLAPPING H-Level-AB≤ #-}

AB≤-refl : {x : AboveBelow A} → x AB≤ x
AB≤-refl {x = bt}   = bt≤
AB≤-refl {x = tp}   = tp≤tp
AB≤-refl {x = wr a} = wr≤wr refl

AB≤-trans : {x y z : AboveBelow A} → x AB≤ y → y AB≤ z → x AB≤ z
AB≤-trans {x = .bt}                            bt≤         yz         = bt≤
AB≤-trans {x = .wr x} {y = .wr y} {z = .wr z} (wr≤wr exy) (wr≤wr ezy) = wr≤wr (exy ∙ ezy)
AB≤-trans {x = .wr x} {y = .wr y} {z = .tp}   (wr≤wr exy)  wr≤tp      = wr≤tp
AB≤-trans {x = .wr x} {y = .tp}   {z = .tp}    wr≤tp       tp≤tp      = wr≤tp
AB≤-trans {x = .tp}   {y = .tp}   {z = .tp}    tp≤tp       tp≤tp      = tp≤tp

AB≤-antisym : {x y : AboveBelow A} → x AB≤ y → y AB≤ x → x ＝ y
AB≤-antisym  bt≤         bt≤      = refl
AB≤-antisym (wr≤wr exy) (wr≤wr _) = ap wr exy
AB≤-antisym  tp≤tp       tp≤tp    = refl

AB≤-dec : ⦃ da : is-discrete A ⦄
        → {x y : AboveBelow A} → Dec (x AB≤ y)
AB≤-dec {x = bt}              = yes bt≤
AB≤-dec {x = tp}   {y = bt}   = no λ ()
AB≤-dec {x = tp}   {y = tp}   = yes tp≤tp
AB≤-dec {x = tp}   {y = wr x} = no λ ()
AB≤-dec {x = wr x} {y = bt}   = no λ ()
AB≤-dec {x = wr x} {y = tp}   = yes wr≤tp
AB≤-dec {x = wr x} {y = wr y} with x ≟ y
... | yes e = yes (wr≤wr e)
... | no ne = no λ where
                    (wr≤wr e) → ne e

-- join

_⊔ab_ : ⦃ da : is-discrete A ⦄
      → AboveBelow A → AboveBelow A → AboveBelow A
bt   ⊔ab y    = y
tp   ⊔ab _    = tp
wr x ⊔ab bt   = wr x
wr _ ⊔ab tp   = tp
wr x ⊔ab wr y = if x =? y then wr x else tp

l≤⊔ab : ⦃ da : is-discrete A ⦄
      → {x y : AboveBelow A}
      → x AB≤ (x ⊔ab y)
l≤⊔ab {x = bt}              = bt≤
l≤⊔ab {x = tp}              = tp≤tp
l≤⊔ab {x = wr x} {y = bt}   = wr≤wr refl
l≤⊔ab {x = wr x} {y = tp}   = wr≤tp
l≤⊔ab {x = wr x} {y = wr y} with x ≟ y
... | yes e = wr≤wr refl
... | no ne = wr≤tp

r≤⊔ab : ⦃ da : is-discrete A ⦄
      → {x y : AboveBelow A}
      → y AB≤ (x ⊔ab y)
r≤⊔ab {x = bt}             = AB≤-refl
r≤⊔ab {x = tp}            = ≤tp
r≤⊔ab {x = wr x} {y = bt} = bt≤
r≤⊔ab {x = wr x} {y = tp} = tp≤tp
r≤⊔ab {x = wr x} {y = wr y} with x ≟ y
... | yes e = wr≤wr (e ⁻¹)
... | no ne = wr≤tp

⊔ab≤ : ⦃ da : is-discrete A ⦄
     → {x y : AboveBelow A}
     → (z : AboveBelow A) → x AB≤ z → y AB≤ z → (x ⊔ab y) AB≤ z
⊔ab≤                          z       bt≤                 yz                 = yz
⊔ab≤ {x = .wr x}             .(wr z) (wr≤wr {y = z} exz)  bt≤                = wr≤wr exz
⊔ab≤ {x = .wr x} {y = .wr y} .(wr z) (wr≤wr {y = z} exz) (wr≤wr {x = y} eyz) with x ≟ y
... | yes _ = wr≤wr exz
... | no ne = absurd (ne (exz ∙ eyz ⁻¹))
⊔ab≤                          z       wr≤tp               yz                 = ≤tp
⊔ab≤                          z       tp≤tp               yz                 = tp≤tp

-- meet

_⊓ab_ : ⦃ da : is-discrete A ⦄
      → AboveBelow A → AboveBelow A → AboveBelow A
bt   ⊓ab _    = bt
tp   ⊓ab y    = y
wr _ ⊓ab bt   = bt
wr x ⊓ab tp   = wr x
wr x ⊓ab wr y = if x =? y then wr x else bt

⊓ab≤l : ⦃ da : is-discrete A ⦄
      → {x y : AboveBelow A}
      → (x ⊓ab y) AB≤ x
⊓ab≤l {x = bt}              = bt≤
⊓ab≤l {x = tp}              = ≤tp
⊓ab≤l {x = wr x} {y = bt}   = bt≤
⊓ab≤l {x = wr x} {y = tp}   = wr≤wr refl
⊓ab≤l {x = wr x} {y = wr y} with x ≟ y
... | yes e = wr≤wr refl
... | no ne = bt≤

⊓ab≤r : ⦃ da : is-discrete A ⦄
      → {x y : AboveBelow A}
      → (x ⊓ab y) AB≤ y
⊓ab≤r {x = bt}              = bt≤
⊓ab≤r {x = tp}              = AB≤-refl
⊓ab≤r {x = wr x} {y = bt}   = bt≤
⊓ab≤r {x = wr x} {y = tp}   = wr≤tp
⊓ab≤r {x = wr x} {y = wr y} with x ≟ y
... | yes e = wr≤wr e
... | no ne = bt≤

≤⊓ab : ⦃ da : is-discrete A ⦄
     → {x y : AboveBelow A}
     → (z : AboveBelow A)
     → z AB≤ x → z AB≤ y → z AB≤ (x ⊓ab y)
≤⊓ab                          .bt     bt≤               zy        = bt≤
≤⊓ab {x = .wr x} {y = .wr y} .(wr z) (wr≤wr {x = z} e) (wr≤wr ez) with x ≟ y
... | yes _ = wr≤wr e
... | no ne = absurd (ne (e ⁻¹ ∙ ez))
≤⊓ab {x = .wr x}             .(wr z) (wr≤wr {x = z} e)  wr≤tp     = wr≤wr e
≤⊓ab {x = .tp}                 z      wr≤tp             zy        = zy
≤⊓ab                           z      tp≤tp             tp≤tp     = tp≤tp

-- well-foundedness

-- TODO reflexive reduction?
_AB<_ : {A : 𝒰 ℓ} → AboveBelow A → AboveBelow A → 𝒰 ℓ
x AB< y = (x AB≤ y) × (x ≠ y)

AB-wf : is-wf (_AB<_ {A = A})
AB-wf bt = acc λ where
                   bt sy → absurd (sy .snd refl)
AB-wf tp = acc λ where
                   bt sy → acc λ where
                                   bt sz → absurd (sz .snd refl)
                   tp sy → absurd (sy .snd refl)
                   (wr y) sy → acc λ where
                                       bt sz → acc λ where
                                                        bt sw → absurd (sw .snd refl)
                                       (wr z) (wr≤wr e , ne) → absurd (ne (ap wr e))
AB-wf (wr x) = acc λ where
                       bt sy → acc λ where
                                   bt sz → absurd (sz .snd refl)
                       (wr y) (wr≤wr e , ne) → absurd (ne (ap wr e))

AB-noeth : is-noeth (_AB<_ {A = A})
AB-noeth bt = acc λ where
                      bt sy → absurd (sy .snd refl)
                      tp sy → acc λ where
                                      tp sz → absurd (sz .snd refl)
                      (wr y) sy → acc λ where
                                          tp sz → acc λ where
                                                          tp sw → absurd (sw .snd refl)
                                          (wr z) (wr≤wr e , ne) → absurd (ne (ap wr e))
AB-noeth tp = acc λ where
                      tp sy → absurd (sy .snd refl)
AB-noeth (wr x) = acc λ where
                          tp sy → acc λ where
                                          tp sz → absurd (sz .snd refl)
                          (wr y) (wr≤wr e , ne) → absurd (ne (ap wr e))

AB-finheight : is-of-finite-height (_AB<_ {A = A})
AB-finheight x = AB-wf x , AB-noeth x

-- instances

AboveBelowₚ : (A : 𝒰 ℓ) → ⦃ H-Level 2 A ⦄ → Poset ℓ ℓ
AboveBelowₚ A      .Poset.Ob        = AboveBelow A
AboveBelowₚ A      .Poset._≤_       = _AB≤_
AboveBelowₚ A      .Poset.≤-thin    = AB≤-prop {sa = hlevel 2}
AboveBelowₚ A      .Poset.≤-refl    = AB≤-refl
AboveBelowₚ A      .Poset.≤-trans   = AB≤-trans
AboveBelowₚ A      .Poset.≤-antisym = AB≤-antisym

instance
  AboveBelow-bottom : ⦃ sa : H-Level 2 A ⦄ → Bottom (AboveBelowₚ A)
  AboveBelow-bottom .Bottom.bot = bt
  AboveBelow-bottom .Bottom.bot-is-bot _ = bt≤

  AboveBelow-top : ⦃ sa : H-Level 2 A ⦄ → Top (AboveBelowₚ A)
  AboveBelow-top .Top.top = tp
  AboveBelow-top .Top.top-is-top _ = ≤tp

  AboveBelow-joins : ⦃ sa : H-Level 2 A ⦄ → ⦃ da : is-discrete A ⦄  -- TODO how to apply Hedberg?
                   → Has-joins (AboveBelowₚ A)
  AboveBelow-joins {x} {y} .Join.lub = x ⊔ab y
  AboveBelow-joins         .Join.has-join .is-join.l≤join = l≤⊔ab
  AboveBelow-joins {x}     .Join.has-join .is-join.r≤join = r≤⊔ab {x = x}
  AboveBelow-joins         .Join.has-join .is-join.least = ⊔ab≤

  AboveBelow-meets : ⦃ sa : H-Level 2 A ⦄ → ⦃ da : is-discrete A ⦄  -- TODO how to apply Hedberg?
                   → Has-meets (AboveBelowₚ A)
  AboveBelow-meets {x} {y} .Meet.glb = x ⊓ab y
  AboveBelow-meets         .Meet.has-meet .is-meet.meet≤l = ⊓ab≤l
  AboveBelow-meets {x}     .Meet.has-meet .is-meet.meet≤r = ⊓ab≤r {x = x}
  AboveBelow-meets         .Meet.has-meet .is-meet.greatest = ≤⊓ab

  AboveBelow-join-slat : ⦃ sa : H-Level 2 A ⦄ → ⦃ da : is-discrete A ⦄  -- TODO how to apply Hedberg?
                       → is-join-semilattice (AboveBelowₚ A)
  AboveBelow-join-slat .is-join-semilattice.has-bottom = AboveBelow-bottom
  AboveBelow-join-slat .is-join-semilattice.has-joins  = AboveBelow-joins

  AboveBelow-meet-slat : ⦃ sa : H-Level 2 A ⦄ → ⦃ da : is-discrete A ⦄  -- TODO how to apply Hedberg?
                       → is-meet-semilattice (AboveBelowₚ A)
  AboveBelow-meet-slat .is-meet-semilattice.has-top   = AboveBelow-top
  AboveBelow-meet-slat .is-meet-semilattice.has-meets = AboveBelow-meets

  AboveBelow-lat : ⦃ sa : H-Level 2 A ⦄ → ⦃ da : is-discrete A ⦄  -- TODO how to apply Hedberg?
                 → is-lattice (AboveBelowₚ A)
  AboveBelow-lat .is-lattice.has-join-slat = AboveBelow-join-slat
  AboveBelow-lat .is-lattice.has-meet-slat = AboveBelow-meet-slat
