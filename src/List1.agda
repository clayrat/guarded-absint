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
open import Data.Dec renaming (elim to elimᵈ)

private variable
  A : 𝒰

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

all2?₁ : (A → A → Bool) → List1 A → List1 A → Bool
all2?₁ f (init₁ ∶+ last₁) (init₂ ∶+ last₂) =
  all id (zip-with f init₁ init₂) and f last₁ last₂

-- properties

length-to-list : {xs : List1 A} → length (to-list xs) ＝ length₁ xs
length-to-list {xs = ix ∶+ lx} = snoc-length ix

length₁-∷₁ : {x : A} {xs : List1 A} → length₁ (x ∷₁ xs) ＝ suc (length₁ xs)
length₁-∷₁ = refl

length₁-++ : {xs ys : List1 A}
           → length₁ (xs ++₁ ys) ＝ length₁ xs + length₁ ys
length₁-++ {xs = ix ∶+ lx} {ys = iy ∶+ ly} = ap suc (++-length ix (lx ∷ iy))

all2?-++₁ : {p : A → A → Bool}
          → {as bs xs ys : List1 A}
          → length₁ as ＝ length₁ xs
          → all2?₁ p (as ++₁ bs) (xs ++₁ ys) ＝ all2?₁ p as xs and all2?₁ p bs ys
all2?-++₁ {p} {ia ∶+ la} {ib ∶+ lb} {ix ∶+ lx} {iy ∶+ ly} e =
    let b1 = all id (zip-with p ia ix)
        b2 = p la lx
        b3 = all id (zip-with p ib iy)
        b4 = p lb ly in
    ap (_and b4) (  ap (all id) (zip-with-++ (suc-inj e))
                  ∙ all?-++ {p = id} {xs = zip-with p ia ix} {ys = zip-with p (la ∷ ib) (lx ∷ iy)}
                  ∙ and-assoc b1 b2 b3 ⁻¹)
  ∙ and-assoc (b1 and b2) b3 b4
