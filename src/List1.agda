module List1 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

private variable
  A : 𝒰

record List1 (A : 𝒰) : 𝒰 where
  constructor _+∶_
  field
    init : List A
    last : A

open List1

_∷₁_ : A → List1 A → List1 A
a ∷₁ (init +∶ last) = (a ∷ init) +∶ last

[_]₁ : A → List1 A
[ a ]₁ = [] +∶ a

infixr 5 _++₁_
_++₁_ : List1 A → List1 A → List1 A
(ix +∶ lx) ++₁ (iy +∶ ly) = (ix ++ lx ∷ iy) +∶ ly

to-list : List1 A → List A
to-list (init +∶ last) = snoc init last

all2?₁ : (A → A → Bool) → List1 A → List1 A → Bool
all2?₁ f (init₁ +∶ last₁) (init₂ +∶ last₂) = all=? f init₁ init₂ and f last₁ last₂
