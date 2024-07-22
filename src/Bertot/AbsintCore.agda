module Bertot.AbsintCore where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.Maybe
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Bertot.State as S
open import Bertot.Lang
open import Bertot.AxSem

module AIntCore
  (A : 𝒰)
  (bot : A)
  (fromN : ℕ → A)                 -- ~ α / abstraction
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)  -- ~ γ / concretization

  where

  open S.State A bot

  a-af : State → AExpr → A
  a-af s (ANum n)      = fromN n
  a-af s (AVar x)      = stlup s x
  a-af s (APlus e₁ e₂) = add (a-af s e₁) (a-af s e₂)

  s→a : State → Assert
  s→a []            = QTrue
  s→a ((x , a) ∷ t) = QConj (to-pred a (AVar x)) (s→a t)

  ms→a : Maybe State → Assert
  ms→a (just s) = s→a s
  ms→a nothing  = QFalse

module AIntCoreSem
  (A : 𝒰)
  (bot : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  (pe : PEnv) {- TODO prop ? -}
  (bot-sem : ∀ {e} → to-pred bot e ＝ QTrue)
  (fromN-sem : ∀ {g x} → ia pe g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ {g v e} → ia pe g (to-pred v e) ＝ ia pe g (to-pred v (ANum (af g e))))
  (a-add-sem : ∀ {g v1 v2 x1 x2}
            → ia pe g (to-pred v1 (ANum x1))
            → ia pe g (to-pred v2 (ANum x2))
            → ia pe g (to-pred (add v1 v2) (ANum (x1 + x2))))
  (subst-to-pred : ∀ {v x e e'} → qsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  where

  open S.State A bot
  open AIntCore A bot fromN add to-pred

  qsubst-no-occur : ∀ {x l e} s
                  → is-true (no-dups s (x ∷ l))
                  → qsubst x e (s→a s) ＝ s→a s
  qsubst-no-occur             []            _ = refl
  qsubst-no-occur {x} {l} {e} ((y , v) ∷ s)   =
    elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l) and no-dups s (y ∷ x ∷ l))
                   → QConj (qsubst x e (to-pred v (AVar y))) (qsubst x e (s→a s)) ＝ QConj (to-pred v (AVar y)) (s→a s)}
      (λ p c → absurd c)
      (λ ¬p h → let h' = and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ x ∷ l)} $ h in
                ap² QConj
                  (  subst-to-pred
                   ∙ ap (to-pred v) (elimᵈ {C = λ q → (if ⌊ q ⌋ then e else AVar y) ＝ AVar y}
                                           (λ p → absurd (¬p p))
                                           (λ _ → refl)
                                           (x ≟ y)))
                  (qsubst-no-occur {l = y ∷ l} s (subst is-true (no-dups-transpose-head {s = s}) (h' .snd))))
      (x ≟ y)

  subst-no-dups : ∀ {g v x e l} s
                → is-true (no-dups s l)
                → ia pe g (s→a s)
                → ia pe g (to-pred v (ANum (af g e)))
                → ia pe g (qsubst x e (s→a (stupd x v s)))
  subst-no-dups {g} {v} {x} {e}     []            h1 h2 h3 =
    subst (ia pe g) (subst-to-pred ⁻¹)
      (discrete-eq {x = x} {C = λ q → ia pe g (to-pred v (if ⌊ q ⌋ then e else AVar x))}
         refl (transport (to-pred-sem ⁻¹) h3)) , tt
  subst-no-dups {g} {v} {x} {e} {l} ((y , w) ∷ s) h1 (h2 , h3) h4 =
    let h5 = (and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ l)} $ h1) .snd in
    elimᵈ {C = λ q → ia pe g (qsubst x e (s→a (if ⌊ q ⌋ then (y , v) ∷ s else (y , w) ∷ stupd x v s)))}
          (λ eq →   subst (ia pe g) (subst-to-pred ⁻¹) (discrete-eq {C = λ q → ia pe g (to-pred v (if ⌊ q ⌋ then e else AVar y))}
                                                         eq (transport (to-pred-sem ⁻¹) h4))
                  , subst (ia pe g) (qsubst-no-occur s (subst (λ q → is-true (no-dups s (q ∷ l))) (eq ⁻¹) h5) ⁻¹) h3)
          (λ ne →   subst (ia pe g) (subst-to-pred ⁻¹) (discrete-ne {C = λ q → ia pe g (to-pred w (if ⌊ q ⌋ then e else AVar y))}
                                                         ne h2)
                  , subst-no-dups s h5 h3 h4)
          (x ≟ y)

  subst-consistent : ∀ {s g v x e}
                   → consistent s
                   → ia pe g (s→a s)
                   → ia pe g (to-pred v (ANum (af g e)))
                   → ia pe g (qsubst x e (s→a (stupd x v s)))
  subst-consistent {s} = subst-no-dups s

  lookup-sem : ∀ {g} s → ia pe g (s→a s)
             → ∀ {x} → ia pe g (to-pred (stlup s x) (ANum (g x)))
  lookup-sem {g} []            tt            = subst (ia pe g) (bot-sem ⁻¹) tt
  lookup-sem {g} ((y , v) ∷ s) (h1 , h2) {x} =
    elimᵈ {C = λ q → ia pe g (to-pred (if ⌊ q ⌋ then v else stlup s x) (ANum (g x)))}
          (λ eq → transport (to-pred-sem ∙ ap (λ q → ia pe g (to-pred v (ANum (g q)))) (eq ⁻¹)) h1)
          (λ _ → lookup-sem s h2)
          (x ≟ y)

  a-af-sound : ∀ {s g} e
             → ia pe g (s→a s)
             → ia pe g (to-pred (a-af s e) (ANum (af g e)))
  a-af-sound     (ANum n)      h = fromN-sem
  a-af-sound {s} (AVar x)      h = lookup-sem s h
  a-af-sound     (APlus e₁ e₂) h = a-add-sem (a-af-sound e₁ h) (a-af-sound e₂ h)

  lookup-sem2 : ∀ {g l} s
              → is-true (no-dups s l)
              → (∀ x → is-true (not (mem x l)) → ia pe g (to-pred (stlup s x) (AVar x)))
              → ia pe g (s→a s)
  lookup-sem2         []            h hp = tt
  lookup-sem2 {g} {l} ((x , v) ∷ s) h hp =
    let hh = and-true-≃ {x = not (mem x l)} {y = no-dups s (x ∷ l)} $ h in
      elimᵈ {C = λ q → (is-true (not (mem x l)) →
                        ia pe g (to-pred (if ⌊ q ⌋ then v else stlup s x) (AVar x))) →
                 ia pe g (to-pred v (AVar x)) }
            (λ _ f → f (hh .fst))
            (λ ¬p → absurd (¬p refl))
            (x ≟ x) (hp x)
    , lookup-sem2 {l = x ∷ l} s (hh .snd)
        λ y my → elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l)) →
                                   ia pe g (to-pred (stlup s y) (AVar y)) }
                       (λ hp my′  → absurd my′)
                       (λ ¬hp my′ → elimᵈ
                                     {C =
                                      λ q → (is-true (not (mem y l)) →
                                             ia pe g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))) →
                                            ia pe g (to-pred (stlup s y) (AVar y))}
                                     (λ ep py  → absurd (¬hp (ep ⁻¹)))
                                     (λ ¬ep py → py my′)
                                     (y ≟ x) (hp y))
                       (x ≟ y) my

  a-upd-ia-all : ∀ {g l x e} s → is-true (no-dups s l)
               → (∀ {y} → y ≠ x → is-true (not (mem y l))
                  → ia pe g (to-pred (stlup s y) (AVar y)))
               → ia pe g (to-pred e (AVar x))
               → ia pe g (s→a (stupd x e s))
  a-upd-ia-all                  []            cs f h = h , tt
  a-upd-ia-all {g} {l} {x} {e} ((z , v) ∷ s) cs     =
    elimᵈ {C = λ q → ({y : String} → y ≠ x → is-true (not (mem y l))
                      → ia pe g (to-pred (if ⌊ y ≟ z ⌋ then v else stlup s y) (AVar y)))
                   → ia pe g (to-pred e (AVar x))
                   → ia pe g (s→a (if ⌊ q ⌋ then (z , e) ∷ s else (z , v) ∷ stupd x e s)) }
          (λ hp  ias iax →   (subst (λ q → ia pe g (to-pred e (AVar q))) hp iax)
                          , lookup-sem2 {l = z ∷ l} s
                             ((and-true-≃ {x = not (mem z l)} {y = no-dups s (z ∷ l)} $ cs) .snd)
                             λ y h → let hh = and-true-≃ {x = not ⌊ z ≟ y ⌋} {y = not (mem y l)} $
                                              subst is-true (not-or ⌊ z ≟ y ⌋ (mem y l)) h in
                               elimᵈ {C = λ q → (y ≠ x →
                                                 is-true (not (mem y l)) →
                                                 ia pe g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))) →
                                                ia pe g (to-pred (stlup s y) (AVar y))}
                                     (λ e  _ → absurd (elimᵈ {C = λ q → is-true (not ⌊ q ⌋) → ⊥}
                                                             (λ _ → id) (λ ¬e′ _ → ¬e′ (e ⁻¹))
                                                             (z ≟ y) (hh .fst)))
                                     (λ ¬e f → f (λ p′ → ¬e (p′ ∙ hp)) (hh .snd))
                                     (y ≟ z)
                                     (ias {y}))
          (λ ¬hp ias iax → let hh = and-true-≃ {x = not (mem z l)} {y = no-dups s (z ∷ l)} $ cs in
                            elimᵈ {C = λ q → ia pe g (to-pred (if ⌊ q ⌋ then v else stlup s z) (AVar z))
                                           → ia pe g (to-pred v (AVar z))}
                                  (λ _  → id)
                                  (λ ¬c → absurd (¬c refl))
                                  (z ≟ z)
                                  (ias (λ w → ¬hp (w ⁻¹)) (hh .fst))
                          , a-upd-ia-all {l = z ∷ l} s (hh .snd)
                               (λ {y} ne h → let h′ = and-true-≃ {x = not ⌊ z ≟ y ⌋} {y = not (mem y l)} $
                                                      subst is-true (not-or ⌊ z ≟ y ⌋ (mem y l)) h in
                                             elimᵈ {C = λ q → ia pe g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))
                                                            → ia pe g (to-pred (stlup s y) (AVar y))}
                                                   (λ yz → absurd (elimᵈ {C = λ q → is-true (not ⌊ q ⌋) → ⊥}
                                                                         (λ _ → id) (λ ¬e′ _ → ¬e′ (yz ⁻¹))
                                                                         (z ≟ y) (h′ .fst)))
                                                   (λ ¬yz → id)
                                                   (y ≟ z)
                                                   (ias ne (h′ .snd)))
                            iax)
          (x ≟ z)

  a-upd-ia-all' : ∀ {g s x e} → consistent s
                → (∀ {y} → y ≠ x → ia pe g (to-pred (stlup s y) (AVar y)))
                → ia pe g (to-pred e (AVar x))
                → ia pe g (s→a (stupd x e s))
  a-upd-ia-all' {s} cs ias = a-upd-ia-all s cs (λ {y} ne _ → ias ne)
