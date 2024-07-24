module Nipkow.State where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

-- membership

-- TODO use elem
mem : String → List String → Bool
mem s []      = false
mem s (x ∷ l) = (⌊ x ≟ s ⌋) or mem s l

mem-transpose : ∀ {z x y l'} l
              → mem z (l ++ x ∷ y ∷ l') ＝ mem z (l ++ y ∷ x ∷ l')
mem-transpose {z} {x} {y} {l'} []      = or-assoc ⌊ x ≟ z ⌋ ⌊ y ≟ z ⌋ (mem z l') ⁻¹
                                       ∙ ap (λ q → q or mem z l') (or-comm  ⌊ x ≟ z ⌋ ⌊ y ≟ z ⌋)
                                       ∙ or-assoc ⌊ y ≟ z ⌋ ⌊ x ≟ z ⌋ (mem z l')
mem-transpose {z}              (h ∷ t) = ap (⌊ h ≟ z ⌋ or_) (mem-transpose t)

mem-more : ∀ {l x a} → is-true (not (mem x (a ∷ l))) → is-true (not (mem x l))
mem-more {l} {x} {a} nm =
  (and-true-≃ {x = not ⌊ a ≟ x ⌋} {y = not (mem x l)} $
   subst is-true (not-or ⌊ a ≟ x ⌋ (mem x l)) nm) .snd

St : 𝒰 → 𝒰
St A = List (String × A)

module State
  (A : 𝒰)
  (top : A)

  where

  -- state infrastructure

  State : 𝒰
  State = St A

  stlup : State → String → A
  stlup []            x = top
  stlup ((y , v) ∷ t) x = if ⌊ x ≟ y ⌋ then v else stlup t x

  stupd : String → A → State → State
  stupd x v []            = (x , v) ∷ []
  stupd x v ((y , w) ∷ t) = if ⌊ x ≟ y ⌋ then (y , v) ∷ t else (y , w) ∷ stupd x v t
