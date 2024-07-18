module List1 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Binary.All2
open import Data.Dec renaming (elim to elimᵈ)

private variable
  A : 𝒰

-- non-empty list with a guaranteed element at the end

record List1 (A : 𝒰) : 𝒰 where
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

-- basic properties
∶+₁-++₁ : {xs : List1 A} {x : A} → xs ∶+₁ x ＝ xs ++₁ [ x ]₁
∶+₁-++₁ {xs = init ∶+ last} {x} = ap (_∶+ x) (snoc-append init)

length-to-list : {xs : List1 A} → length (to-list xs) ＝ length₁ xs
length-to-list {xs = ix ∶+ lx} = snoc-length ix

length₁-∷₁ : {x : A} {xs : List1 A} → length₁ (x ∷₁ xs) ＝ suc (length₁ xs)
length₁-∷₁ = refl

length₁-++ : {xs ys : List1 A}
           → length₁ (xs ++₁ ys) ＝ length₁ xs + length₁ ys
length₁-++ {xs = ix ∶+ lx} {ys = iy ∶+ ly} = ap suc (++-length ix (lx ∷ iy))

-- propositional all2

All2₁ : (A → A → 𝒰) → List1 A → List1 A → 𝒰
All2₁ R (ix ∶+ lx) (iy ∶+ ly) = All2 R ix iy × R lx ly

All2-∶∶₁-l : {R : A → A → 𝒰} {x y : A}
          → {xs ys : List1 A}
          → All2₁ R (x ∷₁ xs) (y ∷₁ ys) → R x y × All2₁ R xs ys
All2-∶∶₁-l {xs = ix ∶+ lx} {ys = iy ∶+ ly} (ri ∷ rs , rl) = ri , (rs , rl)

All2-∶∶₁-r : {R : A → A → 𝒰} {x y : A}
          → {xs ys : List1 A}
          → R x y → All2₁ R xs ys → All2₁ R (x ∷₁ xs) (y ∷₁ ys)
All2-∶∶₁-r {xs = ix ∶+ lx} {ys = iy ∶+ ly} ri (rs , rl) = ri ∷ rs , rl

All2₁-++₁ : {R : A → A → 𝒰}
          → {as bs xs ys : List1 A}
          → All2₁ R as xs → All2₁ R bs ys
          → All2₁ R (as ++₁ bs) (xs ++₁ ys)
All2₁-++₁ {as = ia ∶+ la} {bs = ib ∶+ lb} {xs = ix ∶+ lx} {ys = iy ∶+ ly} (raxs , rax) (rbys , rby) =
  all2-++ raxs (rax ∷ rbys) , rby

All2₁-split : {R : A → A → 𝒰}
            → {as bs xs ys : List1 A}
            → length₁ as ＝ length₁ xs
            → All2₁ R (as ++₁ bs) (xs ++₁ ys)
            → All2₁ R as xs × All2₁ R bs ys
All2₁-split {as = ia ∶+ la} {bs = ib ∶+ lb} {xs = ix ∶+ lx} {ys = iy ∶+ ly} e (rs , rby) with all2-split (suc-inj e) rs
... | raxs , (rax ∷ rbys) = (raxs , rax) , (rbys , rby)

All2₁-∶+₁-l : {R : A → A → 𝒰} {x y : A}
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

All2₁-∶+₁-r : {R : A → A → 𝒰} {x y : A}
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
