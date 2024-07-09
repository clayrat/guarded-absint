module AbsintCore where

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

open import Lang
open import State

module AIntCore
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  where

  open State.State A top

  a-af : State → AExpr → A
  a-af s (ANum n)      = fromN n
  a-af s (AVar x)      = stlup s x
  a-af s (APlus e₁ e₂) = add (a-af s e₁) (a-af s e₂)

  s→a : State → Assert
  s→a []            = QTrue
  s→a ((x , a) ∷ t) = QConj (to-pred a (AVar x)) (s→a t)

  s→a' : Maybe State → Assert
  s→a' (just s) = s→a s
  s→a' nothing  = QFalse

module AIntCoreSem
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  (m : String → List ℕ → 𝒰) {- TODO prop ? -}

  (top-sem : ∀ {e} → to-pred top e ＝ QTrue)
  (fromN-sem : ∀ {g x} → ia m g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ {g v e} → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (a-add-sem : ∀ {g v1 v2 x1 x2}
            → ia m g (to-pred v1 (ANum x1))
            → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))
  (subst-to-pred : ∀ {v x e e'} → qsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  where

  open State.State A top
  open AIntCore A top fromN add to-pred

  qsubst-no-occur : ∀ {x l e} s
                  → is-true (no-dups s (x ∷ l))
                  → qsubst x e (s→a s) ＝ s→a s
  qsubst-no-occur             []            _ = refl
  qsubst-no-occur {x} {l} {e} ((y , v) ∷ s)   =
    elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l) and no-dups s (y ∷ x ∷ l))
                   → QConj (qsubst x e (to-pred v (AVar y))) (qsubst x e (s→a s)) ＝ QConj (to-pred v (AVar y)) (s→a s)}
      (λ p c → absurd c)
      (λ ¬p h → let h' = and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ x ∷ l)} $ is-true≃is-trueₚ $ h in
                ap² QConj
                  (  subst-to-pred
                   ∙ ap (to-pred v) (elimᵈ {C = λ q → (if ⌊ q ⌋ then e else AVar y) ＝ AVar y}
                                           (λ p → absurd (¬p p))
                                           (λ _ → refl)
                                           (x ≟ y)))
                  (qsubst-no-occur {l = y ∷ l} s (is-true≃is-trueₚ ⁻¹ $ subst is-trueₚ (no-dups-transpose-head {s = s}) (h' .snd))))
      (x ≟ y)

  subst-no-dups : ∀ {g v x e l} s
                → is-true (no-dups s l)
                → ia m g (s→a s)
                → ia m g (to-pred v (ANum (af g e)))
                → ia m g (qsubst x e (s→a (stupd x v s)))
  subst-no-dups {g} {v} {x} {e}     []            h1 h2 h3 =
      subst (ia m g) (subst-to-pred ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred v (if ⌊ q ⌋ then e else AVar x))}
                                               (λ _ → transport (to-pred-sem ⁻¹) h3)
                                               (λ ¬p → absurd (¬p refl))
                                               (x ≟ x)) , tt
  subst-no-dups {g} {v} {x} {e} {l} ((y , w) ∷ s) h1 (h2 , h3) h4 =
    let h5 = (and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ l)} $ is-true≃is-trueₚ $ h1) .snd in
    elimᵈ {C = λ q → ia m g (qsubst x e (s→a (if ⌊ q ⌋ then (y , v) ∷ s else (y , w) ∷ stupd x v s)))}
      (λ p  →   subst (ia m g) (subst-to-pred ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred v (if ⌊ q ⌋ then e else AVar y))}
                                                         (λ _ → transport (to-pred-sem ⁻¹) h4)
                                                         (λ ¬p → absurd (¬p p))
                                                         (x ≟ y))
              , subst (ia m g) (qsubst-no-occur s (is-true≃is-trueₚ ⁻¹ $ subst (λ q → is-trueₚ (no-dups s (q ∷ l))) (p ⁻¹) h5) ⁻¹) h3)
      (λ ¬p →   subst (ia m g) (subst-to-pred ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred w (if ⌊ q ⌋ then e else AVar y))}
                                                         (λ p → absurd (¬p p))
                                                         (λ _ → h2)
                                                         (x ≟ y))
              , subst-no-dups s (is-true≃is-trueₚ ⁻¹ $ h5) h3 h4)
      (x ≟ y)

  subst-consistent : ∀ {s g v x e}
                   → consistent s
                   → ia m g (s→a s)
                   → ia m g (to-pred v (ANum (af g e)))
                   → ia m g (qsubst x e (s→a (stupd x v s)))
  subst-consistent {s} = subst-no-dups s

  lookup-sem : ∀ {g} s → ia m g (s→a s)
             → ∀ {x} → ia m g (to-pred (stlup s x) (ANum (g x)))
  lookup-sem {g} []            tt            = subst (ia m g) (top-sem ⁻¹) tt
  lookup-sem {g} ((y , v) ∷ s) (h1 , h2) {x} =
    elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s x) (ANum (g x)))}
          (λ p → transport (to-pred-sem ∙ ap (λ q → ia m g (to-pred v (ANum (g q)))) (p ⁻¹)) h1)
          (λ _ → lookup-sem s h2)
          (x ≟ y)

  a-af-sound : ∀ {s g} e
             → ia m g (s→a s)
             → ia m g (to-pred (a-af s e) (ANum (af g e)))
  a-af-sound     (ANum n)      h = fromN-sem
  a-af-sound {s} (AVar x)      h = lookup-sem s h
  a-af-sound     (APlus e₁ e₂) h = a-add-sem (a-af-sound e₁ h) (a-af-sound e₂ h)

  lookup-sem2 : ∀ {g l} s
              → is-true (no-dups s l)
              → (∀ x → is-true (not (mem x l)) → ia m g (to-pred (stlup s x) (AVar x)))
              → ia m g (s→a s)
  lookup-sem2         []            h p = tt
  lookup-sem2 {g} {l} ((x , v) ∷ s) h p =
    let hh = and-true-≃ {x = not (mem x l)} {y = no-dups s (x ∷ l)} $
             is-true≃is-trueₚ $ h in
      elimᵈ {C = λ q → (is-true (not (mem x l)) →
                        ia m g (to-pred (if ⌊ q ⌋ then v else stlup s x) (AVar x))) →
                 ia m g (to-pred v (AVar x)) }
            (λ _ f → f (is-true≃is-trueₚ ⁻¹ $ hh .fst))
            (λ ¬p → absurd (¬p refl))
            (x ≟ x) (p x)
    , lookup-sem2 {l = x ∷ l} s (is-true≃is-trueₚ ⁻¹ $ hh .snd)
        λ y my → elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l)) →
                                   ia m g (to-pred (stlup s y) (AVar y)) }
                       (λ hp my′  → absurd my′)
                       (λ ¬hp my′ → elimᵈ
                                     {C =
                                      λ q → (is-true (not (mem y l)) →
                                             ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))) →
                                            ia m g (to-pred (stlup s y) (AVar y))}
                                     (λ ep py  → absurd (¬hp (ep ⁻¹)))
                                     (λ ¬ep py → py my′)
                                     (y ≟ x) (p y))
                       (x ≟ y) my

  a-upd-ia-all : ∀ {g l x e} s → is-true (no-dups s l)
               → (∀ {y} → y ≠ x → is-true (not (mem y l))
                  → ia m g (to-pred (stlup s y) (AVar y)))
               → ia m g (to-pred e (AVar x))
               → ia m g (s→a (stupd x e s))
  a-upd-ia-all []            cs f h = h , tt
  a-upd-ia-all {g} {l} {x} {e} ((z , v) ∷ s) cs     =
    elimᵈ {C = λ q → ({y : String} → y ≠ x → is-true (not (mem y l))
                      → ia m g (to-pred (if ⌊ y ≟ z ⌋ then v else stlup s y) (AVar y)))
                   → ia m g (to-pred e (AVar x))
                   → ia m g (s→a (if ⌊ q ⌋ then (z , e) ∷ s else (z , v) ∷ stupd x e s)) }
          (λ p  ias iax →   (subst (λ q → ia m g (to-pred e (AVar q))) p iax)
                          , (lookup-sem2 {l = z ∷ l} s
                             (is-true≃is-trueₚ ⁻¹ $ (and-true-≃ {x = not (mem z l)} {y = no-dups s (z ∷ l)} $ is-true≃is-trueₚ $ cs) .snd)
                             λ y h →
                               let hh = and-true-≃ {x = not ⌊ z ≟ y ⌋} {y = not (mem y l)} $
                                        subst is-trueₚ (not-or ⌊ z ≟ y ⌋ (mem y l)) (is-true≃is-trueₚ $ h) in
                               elimᵈ {C = λ q → (y ≠ x →
                                                 is-true (not (mem y l)) →
                                                 ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))) →
                                                ia m g (to-pred (stlup s y) (AVar y))}
                                     (λ e  _ → absurd (elimᵈ {C = λ q → is-trueₚ (not ⌊ q ⌋) → ⊥}
                                                             (λ _     → false≠true)
                                                             (λ ¬e′ _ → ¬e′ (e ⁻¹))
                                                             (z ≟ y) (hh .fst)))
                                     (λ ¬e f → f (λ p′ → ¬e (p′ ∙ p)) (is-true≃is-trueₚ ⁻¹ $ hh .snd))
                                     (y ≟ z)
                                     (ias {y})))
          (λ ¬p ias iax → let hh = and-true-≃ {x = not (mem z l)} {y = no-dups s (z ∷ l)} $ is-true≃is-trueₚ $ cs in
                            elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s z) (AVar z))
                                           → ia m g (to-pred v (AVar z))}
                                  (λ _  → id)
                                  (λ ¬c → absurd (¬c refl))
                                  (z ≟ z)
                                  (ias (λ w → ¬p (w ⁻¹)) (is-true≃is-trueₚ ⁻¹ $ hh .fst))
                          , a-upd-ia-all {l = z ∷ l} s (is-true≃is-trueₚ ⁻¹ $ hh .snd)
                               (λ {y} ne h → let h′ = and-true-≃ {x = not ⌊ z ≟ y ⌋} {y = not (mem y l)} $
                                                      is-true≃is-trueₚ $ subst is-true (not-or ⌊ z ≟ y ⌋ (mem y l)) h in
                                             elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s y) (AVar y))
                                                            → ia m g (to-pred (stlup s y) (AVar y))}
                                                   (λ yz → absurd (elimᵈ {C = λ q → is-trueₚ (not ⌊ q ⌋) → ⊥}
                                                                         (λ _ → false≠true) (λ ¬e′ _ → ¬e′ (yz ⁻¹))
                                                                         (z ≟ y) (h′ .fst)))
                                                   (λ ¬yz → id)
                                                   (y ≟ z)
                                                   (ias ne (is-true≃is-trueₚ ⁻¹ $ h′ .snd)))
                               iax)
          (x ≟ z)

  a-upd-ia-all' : ∀ {g s x e} → consistent s
                → (∀ {y} → y ≠ x → ia m g (to-pred (stlup s y) (AVar y)))
                → ia m g (to-pred e (AVar x))
                → ia m g (s→a (stupd x e s))
  a-upd-ia-all' {s} cs ias = a-upd-ia-all s cs (λ {y} ne _ → ias ne)
