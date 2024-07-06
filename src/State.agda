module State where

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

St : 𝒰 → 𝒰
St A = List (String × A)

module State
  (A : 𝒰)
  (top : A)

  where

  -- state infrastructure

  State : 𝒰
  State = St A

  no-dups : State → List String → Bool
  no-dups []            l = true
  no-dups ((s , _) ∷ t) l = not (mem s l) and no-dups t (s ∷ l)

  consistent : State → 𝒰
  consistent s = is-true (no-dups s [])

  consistent-prop : (s : State) → is-prop (consistent s)
  consistent-prop s = hlevel 1

  consistent-nil : consistent []
  consistent-nil = tt

  no-dups-transpose : ∀ {l l' x y} s → no-dups s (l ++ x ∷ y ∷ l') ＝ no-dups s (l ++ y ∷ x ∷ l')
  no-dups-transpose     []            = refl
  no-dups-transpose {l} ((z , v) ∷ s) = ap² _and_ (ap not (mem-transpose l)) (no-dups-transpose {l = z ∷ l} s)

  no-dups-transpose-head : ∀ {s l x y} → no-dups s (x ∷ y ∷ l) ＝ no-dups s (y ∷ x ∷ l)
  no-dups-transpose-head {s} = no-dups-transpose {l = []} s

  stlup : State → String → A
  stlup []            x = top
  stlup ((y , v) ∷ t) x = if ⌊ x ≟ y ⌋ then v else stlup t x

  stupd : String → A → State → State
  stupd x v []            = (x , v) ∷ []
  stupd x v ((y , w) ∷ t) = if ⌊ x ≟ y ⌋ then (y , v) ∷ t else (y , w) ∷ stupd x v t

  no-dups-update : ∀ {l x v} s
                 → is-true (not (mem x l))
                 → is-true (no-dups s l)
                 → is-true (no-dups (stupd x v s) l)
  no-dups-update {l} {x}     []            h1 h2 = subst is-true (and-id-r (not (mem x l)) ⁻¹) h1
  no-dups-update {l} {x} {v} ((y , w) ∷ s) h1 h2 =
    elimᵈ {C = λ q → is-true (no-dups (if ⌊ q ⌋ then (y , v) ∷ s else (y , w) ∷ stupd x v s) l)}
          (λ p  → h2)
          (λ ¬p → let h34 = and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ l)} $ is-true-≃ $ h2 in
                  is-true-≃ ⁻¹ $
                  and-true-≃ {x = not (mem y l)} {y = no-dups (stupd x v s) (y ∷ l)} ⁻¹ $
                  ( h34 .fst
                  , (is-true-≃ $ no-dups-update s
                       (elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem x l))}
                              (λ p′ → ¬p (p′ ⁻¹))
                              (λ _ → h1)
                              (y ≟ x))
                       (is-true-≃ ⁻¹ $ h34 .snd))))
          (x ≟ y)

  consistent-update : ∀ {s x v} → consistent s → consistent (stupd x v s)
  consistent-update {s} = no-dups-update s tt
