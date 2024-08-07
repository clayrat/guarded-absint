module List1 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Binary.All2
open import Data.Dec renaming (elim to elimᵈ)

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ

-- non-empty list with a guaranteed element at the end

record List1 (A : 𝒰 ℓ) : 𝒰 ℓ where
  constructor _∶+_
  field
    init : List A
    last : A

open List1

_∷₁_ : A → List1 A → List1 A
a ∷₁ (init ∶+ last) = (a ∷ init) ∶+ last

[_]₁ : A → List1 A
[ a ]₁ = [] ∶+ a

length₁ : List1 A → ℕ
length₁ (init ∶+ _) = suc (length init)

infixr 5 _++₁_
_++₁_ : List1 A → List1 A → List1 A
(ix ∶+ lx) ++₁ (iy ∶+ ly) = (ix ++ lx ∷ iy) ∶+ ly

to-list : List1 A → List A
to-list (init ∶+ last) = snoc init last

_∶+₁_ : List1 A → A → List1 A
xs ∶+₁ x = to-list xs ∶+ x

-- made total by replicating once at 0
replicate₁ : ℕ → A → List1 A
replicate₁  zero   a = [ a ]₁
replicate₁ (suc n) a = replicate n a ∶+ a

-- basic properties
∶+-inj : {A : 𝒰 ℓ} {ix iy : List A} {lx ly : A}
       → ix ∶+ lx ＝ iy ∶+ ly → (ix ＝ iy) × (lx ＝ ly)
∶+-inj e = (ap init e) , (ap last e)

∷₁-inj : {x y : A} {xs ys : List1 A}
       → x ∷₁ xs ＝ y ∷₁ ys → (x ＝ y) × (xs ＝ ys)
∷₁-inj {xs = ix ∶+ lx} {ys = iy ∶+ ly} e =
  let h = ∶+-inj e in
  ∷-head-inj (h .fst) , ap² _∶+_ (∷-tail-inj (h .fst)) (h .snd)

++₁-same-inj : {xs ys zs ws : List1 A}
             → length₁ xs ＝ length₁ ys
             → xs ++₁ zs ＝ ys ++₁ ws → (xs ＝ ys) × (zs ＝ ws)
++₁-same-inj {xs = ix ∶+ lx} {ys = iy ∶+ ly} {zs = iz ∶+ lz} {ws = iw ∶+ lw} le e =
  let e1 = ∶+-inj e
      e2 = ++-same-inj ix iy (suc-inj le) (e1 .fst)
    in
  ap² _∶+_ (e2 .fst) (∷-head-inj (e2 .snd)) , ap² _∶+_ (∷-tail-inj (e2 .snd)) (e1 .snd)

to-list-inj : {xs ys : List1 A}
            → to-list xs ＝ to-list ys
            → xs ＝ ys
to-list-inj {xs = ix ∶+ lx} {ys = iy ∶+ ly} e =
  let h = snoc-inj e in
  ap² _∶+_ (h .fst) (h .snd)

∶+₁-++₁ : {xs : List1 A} {x : A} → xs ∶+₁ x ＝ xs ++₁ [ x ]₁
∶+₁-++₁ {xs = init ∶+ last} {x} = ap (_∶+ x) (snoc-append init)

last-++₁ : {xs ys : List1 A} → last (xs ++₁ ys) ＝ last ys
last-++₁ = refl

length-to-list : {xs : List1 A} → length (to-list xs) ＝ length₁ xs
length-to-list {xs = ix ∶+ lx} = snoc-length ix

length₁-∷₁ : {x : A} {xs : List1 A} → length₁ (x ∷₁ xs) ＝ suc (length₁ xs)
length₁-∷₁ = refl

length₁-++ : {xs ys : List1 A}
           → length₁ (xs ++₁ ys) ＝ length₁ xs + length₁ ys
length₁-++ {xs = ix ∶+ lx} {ys = iy ∶+ ly} = ap suc (++-length ix (lx ∷ iy))

replicate₁-+ : {n m : ℕ} {z : A}
             → 0 < n → 0 < m
             → replicate₁ (n + m) z ＝ replicate₁ n z ++₁ replicate₁ m z
replicate₁-+ {n = zero}                  ltn ltm = absurd (≮z ltn)
replicate₁-+ {n = suc n} {m = zero}      ltn ltm = absurd (≮z ltm)
replicate₁-+ {n = suc n} {m = suc m} {z} ltn ltm = ap (_∶+ z) (replicate-+ {m = suc m})

-- propositional all2

All2₁ : (A → A → 𝒰 ℓ′) → List1 A → List1 A → 𝒰 (level-of-type A ⊔ ℓ′)
All2₁ R (ix ∶+ lx) (iy ∶+ ly) = All2 R ix iy × R lx ly

All2₁-is-of-hlevel
  : (n : HLevel) {xs ys : List1 A} {R : A → A → 𝒰 ℓ′}
  → (∀ x y → is-of-hlevel (suc n) (R x y))
  → is-of-hlevel (suc n) (All2₁ R xs ys)
All2₁-is-of-hlevel n {ix ∶+ lx} {iy ∶+ ly} hl =
  ×-is-of-hlevel (suc n) (All2-is-of-hlevel n hl) (hl lx ly)

-- monotype versions
all2₁-refl : {as : List1 A} {P : A → A → 𝒰 ℓ′}
           → (∀ a → P a a)
           → All2₁ P as as
all2₁-refl {as = ia ∶+ la} pr = all2-refl pr , pr la

all2₁-antisym : {as bs : List1 A}
                {P : A → A → 𝒰 ℓ′}
              → (∀ a b → P a b → P b a → a ＝ b)
              → All2₁ P as bs → All2₁ P bs as → as ＝ bs
all2₁-antisym {as = ia ∶+ la} {bs = ib ∶+ lb} pa (abs , lab) (bas , lba) =
  ap² _∶+_ (all2-antisym pa abs bas) (pa la lb lab lba)

all2₁-trans : {as bs cs : List1 A}
              {P : A → A → 𝒰 ℓ′}
            → (∀ a b c → P a b → P b c → P a c)
            → All2₁ P as bs → All2₁ P bs cs → All2₁ P as cs
all2₁-trans {as = ia ∶+ la} {bs = ib ∶+ lb} {cs = ic ∶+ lc} pr (abs , lab) (bcs , lbc) =
  all2-trans pr abs bcs , pr la lb lc lab lbc

All2-∶∶₁-l : {R : A → A → 𝒰 ℓ′} {x y : A}
          → {xs ys : List1 A}
          → All2₁ R (x ∷₁ xs) (y ∷₁ ys) → R x y × All2₁ R xs ys
All2-∶∶₁-l {xs = ix ∶+ lx} {ys = iy ∶+ ly} (ri ∷ rs , rl) = ri , (rs , rl)

All2-∶∶₁-r : {R : A → A → 𝒰 ℓ′} {x y : A}
          → {xs ys : List1 A}
          → R x y → All2₁ R xs ys → All2₁ R (x ∷₁ xs) (y ∷₁ ys)
All2-∶∶₁-r {xs = ix ∶+ lx} {ys = iy ∶+ ly} ri (rs , rl) = ri ∷ rs , rl

All2₁-++₁ : {R : A → A → 𝒰 ℓ′}
          → {as bs xs ys : List1 A}
          → All2₁ R as xs → All2₁ R bs ys
          → All2₁ R (as ++₁ bs) (xs ++₁ ys)
All2₁-++₁ {as = ia ∶+ la} {bs = ib ∶+ lb} {xs = ix ∶+ lx} {ys = iy ∶+ ly} (raxs , rax) (rbys , rby) =
  all2-++ raxs (rax ∷ rbys) , rby

All2₁-split : {R : A → A → 𝒰 ℓ′}
            → {as bs xs ys : List1 A}
            → length₁ as ＝ length₁ xs
            → All2₁ R (as ++₁ bs) (xs ++₁ ys)
            → All2₁ R as xs × All2₁ R bs ys
All2₁-split {as = ia ∶+ la} {bs = ib ∶+ lb} {xs = ix ∶+ lx} {ys = iy ∶+ ly} e (rs , rby) with all2-split (suc-inj e) rs
... | raxs , (rax ∷ rbys) = (raxs , rax) , (rbys , rby)

All2₁-∶+₁-l : {R : A → A → 𝒰 ℓ′} {x y : A}
           → {xs ys : List1 A}
           → length₁ xs ＝ length₁ ys
           → All2₁ R (xs ∶+₁ x) (ys ∶+₁ y)
           → All2₁ R xs ys × R x y
All2₁-∶+₁-l {R} {x} {y} {xs} {ys} e rs =
  let h = All2₁-split e $
          subst (λ q → All2₁ R q (ys ++₁ [ y ]₁)) ∶+₁-++₁ $
          subst (All2₁ R (xs ∶+₁ x)) ∶+₁-++₁ rs
    in
  h .fst , h .snd .snd

All2₁-∶+₁-r : {R : A → A → 𝒰 ℓ} {x y : A}
           → {xs ys : List1 A}
           → All2₁ R xs ys → R x y
           → All2₁ R (xs ∶+₁ x) (ys ∶+₁ y)
All2₁-∶+₁-r {R} {x} {y} {xs} {ys} rs r =
  subst (All2₁ R (xs ∶+₁ x)) (∶+₁-++₁ ⁻¹) $
  subst (λ q → All2₁ R q (ys ++₁ [ y ]₁)) (∶+₁-++₁ ⁻¹) $
  All2₁-++₁ rs ([] , r)

-- boolean all2

all2?₁ : (A → A → Bool) → List1 A → List1 A → Bool
all2?₁ f (init₁ ∶+ last₁) (init₂ ∶+ last₂) =
  all id (zip-with f init₁ init₂) and f last₁ last₂

all2?-∶∶₁ : {r : A → A → Bool} {x y : A}
         → {xs ys : List1 A}
         → all2?₁ r (x ∷₁ xs) (y ∷₁ ys) ＝ r x y and all2?₁ r xs ys
all2?-∶∶₁ {r} {x} {y} {ix ∶+ lx} {iy ∶+ ly} = and-assoc (r x y) (all id (zip-with r ix iy)) (r lx ly)

all2?-++₁ : {r : A → A → Bool}
          → {as bs xs ys : List1 A}
          → length₁ as ＝ length₁ xs
          → all2?₁ r (as ++₁ bs) (xs ++₁ ys) ＝ all2?₁ r as xs and all2?₁ r bs ys
all2?-++₁ {r} {ia ∶+ la} {ib ∶+ lb} {ix ∶+ lx} {iy ∶+ ly} e =
    let b1 = all id (zip-with r ia ix)
        b2 = r la lx
        b3 = all id (zip-with r ib iy)
        b4 = r lb ly in
    ap (_and b4) (  ap (all id) (zip-with-++ (suc-inj e))
                  ∙ all?-++ {p = id} {xs = zip-with r ia ix} {ys = zip-with r (la ∷ ib) (lx ∷ iy)}
                  ∙ and-assoc b1 b2 b3 ⁻¹)
  ∙ and-assoc (b1 and b2) b3 b4

all2?-∶+₁ : {r : A → A → Bool} {x y : A}
         → {xs ys : List1 A}
         → length₁ xs ＝ length₁ ys
         → all2?₁ r (xs ∶+₁ x) (ys ∶+₁ y) ＝ all2?₁ r xs ys and r x y
all2?-∶+₁ {r} {x} {y} {xs} {ys} e = ap² (all2?₁ r) (∶+₁-++₁ {xs = xs}) (∶+₁-++₁ {xs = ys}) ∙ all2?-++₁ e

