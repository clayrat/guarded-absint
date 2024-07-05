module Absint where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Lang

module AInt
  (A : 𝒰)
  (top : A)
  (fromN : ℕ → A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)

  (m : String → List ℕ → 𝒰) {- TODO prop ? -}

  (top-sem : ∀ e → to-pred top e ＝ QTrue)
  (fromN-sem : ∀ g x → ia m g (to-pred (fromN x) (ANum x)))
  (to-pred-sem : ∀ g v e → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (subst-to-pred : ∀ v x e e' → xsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  (a-add-sem : ∀ g v1 v2 x1 x2
            → ia m g (to-pred v1 (ANum x1))
            → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))

  where

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

  -- state infrastructure

  State : 𝒰
  State = List (String × A)

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

  -- abstract interpreter

  a-af : State → AExpr → A
  a-af s (ANum n)      = fromN n
  a-af s (AVar x)      = stlup s x
  a-af s (APlus e₁ e₂) = add (a-af s e₁) (a-af s e₂)

  s→a : State → Assert
  s→a []            = QTrue
  s→a ((x , a) ∷ t) = QConj (to-pred a (AVar x)) (s→a t)

  ab1 : Instr → State → AnInstr × State
  ab1 (Assign x e) s =
    (AnPre (s→a s) (AnAssign x e)) , stupd x (a-af s e) s
  ab1 (Seq i₁ i₂)  s =
    let (ai₁ , s₁) = ab1 i₁ s
        (ai₂ , s₂) = ab1 i₂ s₁
     in
    AnSeq ai₁ ai₂ , s₂
  ab1 (While b i)  s =
    let (ai , _) = ab1 i [] in
    AnWhile b (s→a []) ai , []

  lookup-sem : ∀ {g} s → ia m g (s→a s)
             → ∀ {x} → ia m g (to-pred (stlup s x) (ANum (g x)))
  lookup-sem {g} []            tt            = subst (ia m g) (top-sem (ANum (g _)) ⁻¹) tt
  lookup-sem {g} ((y , v) ∷ s) (h1 , h2) {x} =
    elimᵈ {C = λ q → ia m g (to-pred (if ⌊ q ⌋ then v else stlup s x) (ANum (g x)))}
          (λ p → transport (to-pred-sem g v (AVar y) ∙ ap (λ q → ia m g (to-pred v (ANum (g q)))) (p ⁻¹)) h1)
          (λ _ → lookup-sem s h2)
          (x ≟ y)

  xsubst-no-occur : ∀ {x l e} s
                  → is-true (no-dups s (x ∷ l))
                  → xsubst x e (s→a s) ＝ s→a s
  xsubst-no-occur             []            _ = refl
  xsubst-no-occur {x} {l} {e} ((y , v) ∷ s)   =
    elimᵈ {C = λ q → is-true (not (⌊ q ⌋ or mem y l) and no-dups s (y ∷ x ∷ l))
                   → QConj (xsubst x e (to-pred v (AVar y))) (xsubst x e (s→a s)) ＝ QConj (to-pred v (AVar y)) (s→a s)}
      (λ p c → absurd c)
      (λ ¬p h → let h' = and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ x ∷ l)} $ is-true-≃ $ h in
                ap² QConj
                  (  subst-to-pred v x (AVar y) e
                   ∙ ap (to-pred v) (elimᵈ {C = λ q → (if ⌊ q ⌋ then e else AVar y) ＝ AVar y}
                                           (λ p → absurd (¬p p))
                                           (λ _ → refl)
                                           (x ≟ y)))
                  (xsubst-no-occur {l = y ∷ l} s (is-true-≃ ⁻¹ $ subst is-trueₚ (no-dups-transpose-head {s = s}) (h' .snd))))
      (x ≟ y)

  subst-no-dups : ∀ {g v x e l} s
                → is-true (no-dups s l)
                → ia m g (s→a s)
                → ia m g (to-pred v (ANum (af g e)))
                → ia m g (xsubst x e (s→a (stupd x v s)))
  subst-no-dups {g} {v} {x} {e}     []            h1 h2 h3 =
      subst (ia m g) (subst-to-pred _ _ (AVar _) _ ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred v (if ⌊ q ⌋ then e else AVar x))}
                                                              (λ _ → transport (to-pred-sem g v e ⁻¹) h3)
                                                              (λ ¬p → absurd (¬p refl))
                                                              (x ≟ x))
    , tt
  subst-no-dups {g} {v} {x} {e} {l} ((y , w) ∷ s) h1 (h2 , h3) h4 =
    let h5 = (and-true-≃ {x = not (mem y l)} {y = no-dups s (y ∷ l)} $ is-true-≃ $ h1) .snd in
    elimᵈ {C = λ q → ia m g (xsubst x e (s→a (if ⌊ q ⌋ then (y , v) ∷ s else (y , w) ∷ stupd x v s)))}
      (λ p  →   subst (ia m g) (subst-to-pred v x (AVar y) e ⁻¹) (elimᵈ {C = λ q → ia m g (to-pred v (if ⌊ q ⌋ then e else AVar y))}
                                                                        (λ _ → transport (to-pred-sem g v e ⁻¹) h4)
                                                                        (λ ¬p → absurd (¬p p))
                                                                        (x ≟ y))
              , subst (ia m g) (xsubst-no-occur s (is-true-≃ ⁻¹ $ subst (λ q → is-trueₚ (no-dups s (q ∷ l))) (p ⁻¹) h5) ⁻¹) h3)
      (λ ¬p →   subst (ia m g) (subst-to-pred w x (AVar y) e ⁻¹) (elimᵈ {C = λ q →  ia m g (to-pred w (if ⌊ q ⌋ then e else AVar y))}
                                                                        (λ p → absurd (¬p p))
                                                                        (λ _ → h2)
                                                                        (x ≟ y))
              , subst-no-dups s (is-true-≃ ⁻¹ $ h5) h3 h4)
      (x ≟ y)

  subst-consistent : ∀ {s g v x e}
                   → consistent s
                   → ia m g (s→a s)
                   → ia m g (to-pred v (ANum (af g e)))
                   → ia m g (xsubst x e (s→a (stupd x v s)))
  subst-consistent {s} = subst-no-dups s

  ab1-pc : ∀ {i' s s'} i
         → ab1 i s ＝ (i' , s')
         → ∀ {g a} → ia m g (s→a s) → ia m g (pc i' a)
  ab1-pc     (Assign x e) h1 {g} {a} h2 =
    subst (λ q → ia m g (pc q a)) (ap fst h1) h2
  ab1-pc {s} (Seq i₁ i₂)  h1 {g} {a} h2 =
    subst (λ q → ia m g (pc q a)) (ap fst h1) $
    ab1-pc i₁ refl h2
  ab1-pc     (While b i)  h1 {g} {a} h2 =
    subst (λ q → ia m g (pc q a)) (ap fst h1) tt


  a-af-sound : ∀ {s g} e
             → ia m g (s→a s)
             → ia m g (to-pred (a-af s e) (ANum (af g e)))
  a-af-sound     (ANum n)      h = fromN-sem _ n
  a-af-sound {s} (AVar x)      h = lookup-sem s h
  a-af-sound {s} (APlus e₁ e₂) h = a-add-sem _ (a-af s e₁) (a-af s e₂) (af _ e₁) (af _ e₂) (a-af-sound e₁ h) (a-af-sound e₂ h)
