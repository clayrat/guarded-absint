module Bertot.Lang where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

{- The programming language -}

data AExpr : 𝒰 where
  ANum  : ℕ → AExpr
  AVar  : String → AExpr
  APlus : AExpr → AExpr → AExpr

data BExpr : 𝒰 where
  BLt : AExpr → AExpr → BExpr

data Instr : 𝒰 where
  Assign : String → AExpr → Instr
  Seq    : Instr → Instr → Instr
  While  : BExpr → Instr → Instr

af : (String → ℕ) → AExpr → ℕ
af g (ANum n)      = n
af g (AVar x)      = g x
af g (APlus e₁ e₂) = af g e₁ + af g e₂

bf : (String → ℕ) → BExpr → Bool
bf g (BLt e₁ e₂) = af g e₁ <ᵇ af g e₂

{- Weakest pre-condition calculus -}

data Assert : 𝒰 where
  QPred  : String → List AExpr → Assert
  QB     : BExpr → Assert
  QConj  : Assert → Assert → Assert
  QNot   : Assert → Assert
  QTrue  : Assert
  QFalse : Assert

{- computation of the property associated to an assertion -}
ia : (String → List ℕ → 𝒰) → (String → ℕ) → Assert → 𝒰
ia m g (QPred s l)   = m s (map (af g) l)
ia m g (QB b)        = is-true (bf g b)
ia m g (QConj a₁ a₂) = ia m g a₁ × ia m g a₂
ia m g (QNot a)      = ¬ (ia m g a)
ia m g  QTrue        = ⊤
ia m g  QFalse       = ⊥

ia-prop : {m : String → List ℕ → 𝒰} {g : String → ℕ} (a : Assert)
        → ((s : String) → (l : List ℕ) → is-prop (m s l))
        → is-prop (ia m g a)
ia-prop {g} (QPred s l)   m-prop = m-prop s (map (af g) l)
ia-prop     (QB b)        _      = hlevel 1
ia-prop     (QConj a₁ a₂) m-prop = ×-is-of-hlevel 1 (ia-prop a₁ m-prop) (ia-prop a₂ m-prop)
ia-prop     (QNot a)      _      = hlevel 1
ia-prop      QTrue        _      = hlevel 1
ia-prop      QFalse       _      = hlevel 1

{- Annotated instruction -}

data AnInstr : 𝒰 where
  AnPre    : Assert → AnInstr → AnInstr
  AnAssign : String → AExpr → AnInstr
  AnSeq    : AnInstr → AnInstr → AnInstr
  AnWhile  : BExpr → Assert → AnInstr → AnInstr

cleanup : AnInstr → Instr
cleanup (AnPre _ i)     = cleanup i
cleanup (AnAssign x e)  = Assign x e
cleanup (AnSeq i₁ i₂)   = Seq (cleanup i₁) (cleanup i₂)
cleanup (AnWhile b a i) = While b (cleanup i)

{- computation of the pre-condition for an annotated instruction and a post-condition -}

asubst : String → AExpr → AExpr → AExpr
asubst _ _ e@(ANum _)      = e
asubst x s e@(AVar y)      = if ⌊ x ≟ y ⌋ then s else e
asubst x s   (APlus e₁ e₂) = APlus (asubst x s e₁) (asubst x s e₂)

bsubst : String → AExpr → BExpr → BExpr
bsubst x s (BLt e₁ e₂) = BLt (asubst x s e₁) (asubst x s e₂)

qsubst : String → AExpr → Assert → Assert
qsubst x s (QPred p l)   = QPred p (map (asubst x s) l)
qsubst x s (QB b)        = QB (bsubst x s b)
qsubst x s (QConj a₁ a₂) = QConj (qsubst x s a₁) (qsubst x s a₂)
qsubst x s (QNot a)      = QNot (qsubst x s a)
qsubst _ _  QTrue        = QTrue
qsubst _ _  QFalse       = QFalse

pc : AnInstr → Assert → Assert
pc (AnPre a _)     _    = a
pc (AnAssign x e)  post = qsubst x e post
pc (AnSeq i₁ i₂)   post = pc i₁ (pc i₂ post)
pc (AnWhile _ a _) _    = a

{- A verification condition generator -}

record Cond : 𝒰 where
  constructor imp
  field
    c₁ : Assert
    c₂ : Assert

open Cond

vc : AnInstr → Assert → List Cond
vc (AnPre a i)     post = imp a (pc i post) ∷ vc i post
vc (AnAssign _ _)  _    = []
vc (AnSeq i₁ i₂)   post = vc i₁ (pc i₂ post) ++ vc i₂ post
vc (AnWhile b a i) post = imp (QConj a (QB b)) (pc i a) ∷ imp (QConj a (QNot (QB b))) post ∷ vc i a

-- TODO rewrite via All?
valid : (String → List ℕ → 𝒰) → List Cond → 𝒰
valid m []      = ⊤
valid m (h ∷ t) = (∀ (g : String → ℕ) → ia m g (h .c₁) → ia m g (h .c₂)) × valid m t

valid-prop : {m : String → List ℕ → 𝒰} → (l : List Cond)
           → ((s : String) → (l : List ℕ) → is-prop (m s l))
           → is-prop (valid m l)
valid-prop []      _      = hlevel 1
valid-prop (h ∷ l) m-prop = ×-is-of-hlevel 1
                              (Π-is-of-hlevel 1 λ g → fun-is-of-hlevel 1 (ia-prop (h .c₂) m-prop))
                              (valid-prop l m-prop)

{- A monotonicity property -}

subst-sound-a : {g : String → ℕ} {e₀ : AExpr} {x : String}
              → (e : AExpr)
              → af g (asubst x e₀ e) ＝ af (λ y → if ⌊ x ≟ y ⌋ then af g e₀ else g y) e
subst-sound-a              (ANum n)      = refl
subst-sound-a {g} {e₀} {x} (AVar y)      =
  elimᵈ {C = λ q → af g (if ⌊ q ⌋ then e₀ else AVar y) ＝ (if ⌊ q ⌋ then af g e₀ else g y)}
        (λ _ → refl)
        (λ _ → refl)
        (x ≟ y)
subst-sound-a              (APlus e₁ e₂) =
  ap² _+_ (subst-sound-a e₁) (subst-sound-a e₂)

subst-sound-b : {g : String → ℕ} {e : AExpr} {x : String}
              → (b : BExpr)
              → bf g (bsubst x e b) ＝ bf (λ y → if ⌊ x ≟ y ⌋ then af g e else g y) b
subst-sound-b (BLt e₁ e₂) = ap² _<ᵇ_ (subst-sound-a e₁) (subst-sound-a e₂)

subst-sound-l : {g : String → ℕ} {e : AExpr} {x : String}
              → (l : List AExpr)
              → map (af g) (map (asubst x e) l) ＝ map (af (λ y → if ⌊ x ≟ y ⌋ then af g e else g y)) l
subst-sound-l []      = refl
subst-sound-l (h ∷ t) = ap² _∷_ (subst-sound-a h) (subst-sound-l t)

subst-sound : {m : String → List ℕ → 𝒰} {g : String → ℕ} {e : AExpr} {x : String}
            → (a : Assert)
            → ia m g (qsubst x e a) ＝ ia m (λ y → if ⌊ x ≟ y ⌋ then af g e else g y) a
subst-sound {m} (QPred s l)   = ap (m s) (subst-sound-l l)
subst-sound     (QB b)        = ap is-true (subst-sound-b b)
subst-sound     (QConj a₁ a₂) = ap² _×_ (subst-sound a₁) (subst-sound a₂)
subst-sound     (QNot a)      = ap ¬_ (subst-sound a)
subst-sound      QTrue        = refl
subst-sound      QFalse       = refl

valid-cat : ∀ {m l2} (l1 : List Cond)
          → valid m l1 → valid m l2 → valid m (l1 ++ l2)
valid-cat []             v1  v2 = v2
valid-cat (x ∷ l1) (vx , v1) v2 = vx , valid-cat l1 v1 v2

valid-cat-inv : ∀ {m l2} (l1 : List Cond)
              → valid m (l1 ++ l2)
              → valid m l1 × valid m l2
valid-cat-inv []       vc        = tt , vc
valid-cat-inv (x ∷ l1) (vx , vc) =
  let (ih1 , ih2) = valid-cat-inv l1 vc in
  (vx , ih1) , ih2

vc-monotonic : ∀ {m p1 p2} → (i : AnInstr)
             → valid m (vc i p1) → (∀ g → ia m g p1 → ia m g p2)
             → valid m (vc i p2) × (∀ g → ia m g (pc i p1) → ia m g (pc i p2))
vc-monotonic           (AnPre a i)    (v12 , vc)       p12 =
  let (ih1 , ih2) = vc-monotonic i vc p12 in
  ((λ g → ih2 g ∘ v12 g) , ih1) , λ g → id
vc-monotonic {p1} {p2} (AnAssign x e)  tt              p12 =
  tt , λ g z → transport (subst-sound p2 ⁻¹) (p12 (λ y → if ⌊ x ≟ y ⌋ then af g e else g y) (transport (subst-sound p1) z))
vc-monotonic {p1} {p2} (AnSeq i₁ i₂)   v               p12 =
  let (v1   , v2)   = valid-cat-inv (vc i₁ (pc i₂ p1)) v
      (ih21 , ih22) = vc-monotonic i₂ v2 p12
      (ih11 , ih12) = vc-monotonic {p1 = pc i₂ p1} i₁ v1 ih22
    in
  valid-cat (vc i₁ (pc i₂ p2)) ih11 ih21 , ih12
vc-monotonic           (AnWhile b a i) (v12 , vn , vc) p12 =
  (v12 , (λ g → p12 g ∘ vn g) , vc) , λ g → id
