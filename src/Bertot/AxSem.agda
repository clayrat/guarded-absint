module Bertot.AxSem where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Reflects
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.Dec renaming (elim to elimᵈ)

open import Bertot.Lang
open import Bertot.OpSem

af : (String → ℕ) → AExpr → ℕ
af g (ANum n)      = n
af g (AVar x)      = g x
af g (APlus e₁ e₂) = af g e₁ + af g e₂

bf : (String → ℕ) → BExpr → Bool
bf g (BLt e₁ e₂) = af g e₁ <ᵇ af g e₂

PEnv : 𝒰 (ℓsuc 0ℓ)
PEnv = List (String × (List ℕ → 𝒰))

fp : PEnv → String → List ℕ → 𝒰
fp []            s args = ⊤
fp ((a , m) ∷ p) s args = if ⌊ a ≟ s ⌋ then m args else fp p s args

fp-prop : {p : PEnv} {s : String} {args : List ℕ}
        → (All (λ sf → (l : List ℕ) → is-prop (sf .snd l)) p)
        → is-prop (fp p s args)
fp-prop {p = []}                          pp  = hlevel 1
fp-prop {p = (a , m) ∷ p} {s} {args} (h ∷ pp) =
  elimᵈ {C = λ q → is-prop (if ⌊ q ⌋ then m args else fp p s args)}
        (λ eq → h args)
        (λ ctra → fp-prop pp)
        (a ≟ s)

{- Weakest pre-condition calculus -}

{- computation of the property associated to an assertion -}
ia : PEnv → (String → ℕ) → Assert → 𝒰
ia p g (QPred s l)   = fp p s (map (af g) l)
ia p g (QB b)        = is-true (bf g b)
ia p g (QConj a₁ a₂) = ia p g a₁ × ia p g a₂
ia p g (QNot a)      = ¬ (ia p g a)
ia p g  QTrue        = ⊤
ia p g  QFalse       = ⊥

ia-prop : {p : PEnv} {g : String → ℕ} (a : Assert)
        → (All (λ sf → (l : List ℕ) → is-prop (sf .snd l)) p)
        → is-prop (ia p g a)
ia-prop {g} (QPred s l)   p-prop = fp-prop p-prop
ia-prop     (QB b)        _      = hlevel 1
ia-prop     (QConj a₁ a₂) p-prop = ×-is-of-hlevel 1 (ia-prop a₁ p-prop) (ia-prop a₂ p-prop)
ia-prop     (QNot a)      _      = hlevel 1
ia-prop      QTrue        _      = hlevel 1
ia-prop      QFalse       _      = hlevel 1

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
pc  AnSkip         post = post
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
vc  AnSkip         _    = []
vc (AnAssign _ _)  _    = []
vc (AnSeq i₁ i₂)   post = vc i₁ (pc i₂ post) ++ vc i₂ post
vc (AnWhile b a i) post = imp (QConj a (QB b)) (pc i a) ∷ imp (QConj a (QNot (QB b))) post ∷ vc i a

ic : PEnv → (String → ℕ) → Cond → 𝒰
ic p g (imp c₁ c₂) = ia p g c₁ → ia p g c₂

ic-prop : {p : PEnv} {g : String → ℕ} {c : Cond}
        → (All (λ sf → (l : List ℕ) → is-prop (sf .snd l)) p)
        → is-prop (ic p g c)
ic-prop {c} pp = fun-is-of-hlevel 1 (ia-prop (c .c₂) pp)

valid : PEnv → Cond → 𝒰
valid p c = ∀ {g} → ic p g c

valid-prop : {p : PEnv} {c : Cond}
           → (All (λ sf → (l : List ℕ) → is-prop (sf .snd l)) p)
           → is-prop (valid p c)
valid-prop {c} pp = ∀-is-of-hlevel 1 λ g → ic-prop {c = c} pp

{- Axiomatic semantics -}

data AxSem (preds : PEnv) : Assert → Instr → Assert → 𝒰 where
  AxSkip   : ∀ {p} → AxSem preds p Skip p
  AxAssign : ∀ {p} {x} {e} → AxSem preds (qsubst x e p) (Assign x e) p
  AxSeq    : ∀ {p q r i1 i2}
           → AxSem preds p i1 q → AxSem preds q i2 r → AxSem preds p (Seq i1 i2) r
  AxWhile  : ∀ {p b i}
           → AxSem preds (QConj p (QB b)) i p
           → AxSem preds p (While b i) (QConj p (QNot (QB b)))
  AxConseq : ∀ {p p' q' q i}
           → valid preds (imp p p')
           → AxSem preds p' i q'
           → valid preds (imp q' q)
           → AxSem preds p i q

data NAx (preds : PEnv) : Assert → Instr → Assert → 𝒰 where
  NAxSkip   : ∀ {p q} → valid preds (imp p q) → NAx preds p Skip q
  NAxAssign : ∀ {p p' q x e}
            → valid preds (imp p (qsubst x e p'))
            → valid preds (imp p' q)
            → NAx preds p (Assign x e) q
  NAxSeq    : ∀ {p p' q' r' r i1 i2}
            → valid preds (imp p p')
            → valid preds (imp r' r)
            → NAx preds p' i1 q'
            → NAx preds q' i2 r'
            → NAx preds p (Seq i1 i2) r
  NAxWhile  : ∀ {p p' q b i}
            → valid preds (imp p p')
            → valid preds (imp (QConj p' (QNot (QB b))) q)
            → NAx preds (QConj p' (QB b)) i p'
            → NAx preds p (While b i) q

ax-sem→nax : ∀ {m p i q}
           → AxSem m p i q → NAx m p i q
ax-sem→nax      AxSkip             = NAxSkip id
ax-sem→nax {q}  AxAssign           = NAxAssign {p' = q} id id
ax-sem→nax     (AxSeq as1 as2)     = NAxSeq id id (ax-sem→nax as1) (ax-sem→nax as2)
ax-sem→nax     (AxWhile as)        = NAxWhile id id (ax-sem→nax as)
ax-sem→nax     (AxConseq h1 as h2) with ax-sem→nax as
... | NAxSkip v            = NAxSkip λ h → h2 (v (h1 h))
... | NAxAssign {p'} v1 v2 = NAxAssign {p' = p'} (λ h → v1 (h1 h)) λ h → h2 (v2 h)
... | NAxSeq v1 v2 n1 n2   = NAxSeq (λ h → v1 (h1 h)) (λ h → h2 (v2 h)) n1 n2
... | NAxWhile v1 v2 n     = NAxWhile (λ h → v1 (h1 h)) (λ h → h2 (v2 h)) n

nax→ax-sem : ∀ {m p i q}
           → NAx m p i q → AxSem m p i q
nax→ax-sem {q} (NAxSkip v)                    = AxConseq {p' = q} v AxSkip id
nax→ax-sem     (NAxAssign {p'} {x} {e} v1 v2) = AxConseq {p' = qsubst x e p'} {q' = p'} v1 AxAssign v2
nax→ax-sem     (NAxSeq v1 v2 na1 na2)         = AxConseq v1 (AxSeq (nax→ax-sem na1) (nax→ax-sem na2)) v2
nax→ax-sem     (NAxWhile v1 v2 na)            = AxConseq v1 (AxWhile (nax→ax-sem na)) v2

{- Correctness proofs: axiomatic semantics is correct. -}

af-correct : ∀ {r1 e v g} → AEval r1 e v → af (e→f r1 g) e ＝ v
af-correct          AEN                       = refl
af-correct {v} {g} (AEVar1 {r} {x})           =
  discrete-eq {x = x} {C = λ q → (if ⌊ q ⌋ then v else e→f r g x) ＝ v} refl refl
af-correct {v} {g} (AEVar2 {r} {x} {y} {v = v'} ne a) =
  discrete-ne {C = λ q → (if ⌊ q ⌋ then v' else e→f r g x) ＝ v} (ne ∘ _⁻¹) (af-correct a)
af-correct         (AEPlus a₁ a₂)             =
  ap² _+_ (af-correct a₁) (af-correct a₂)

update-af : ∀ {x v r1 r2 g}
          → SUpdate r1 x v r2 → af (e→f r2 g) (AVar x) ＝ v
update-af {x} {v} {g} (SUp1 {r})                         =
  discrete-eq {x = x} {C = λ q → (if ⌊ q ⌋ then v else e→f r g x) ＝ v} refl refl
update-af {x} {v} {g} (SUp2 {r} {r'} {y} {v = v'} su ne) =
  discrete-ne {C = λ q → (if ⌊ q ⌋ then v' else e→f r' g x) ＝ v} (ne ∘ _⁻¹) (update-af su)

update-af-diff : ∀ {x v r1 r2 g s}
               → SUpdate r1 x v r2 → x ≠ s
               → af (e→f r2 g) (AVar s) ＝ af (e→f r1 g) (AVar s)
update-af-diff {x} {v} {g} {s} (SUp1 {r} {v = v'})                 ne =
  discrete-ne {C = λ q → (if ⌊ q ⌋ then v else e→f r g s) ＝ (if ⌊ q ⌋ then v' else e→f r g s)} ne refl
update-af-diff {x} {v} {g} {s} (SUp2 {r} {r'} {y} {v = v'} su ney) ne =
  elimᵈ {C = λ q → (if ⌊ q ⌋ then v' else e→f r' g s) ＝ (if ⌊ q ⌋ then v' else e→f r g s)}
   (λ _ → refl)
   (λ _ → update-af-diff su ne)
   (y ≟ s)

update-af-var-subst : ∀ {r1 x v r2 e g s}
                    → SUpdate r1 x v r2 → AEval r1 e v
                    → af (e→f r2 g) (AVar s) ＝ af (e→f r1 g) (asubst x e (AVar s))
update-af-var-subst {r1} {x} {v} {r2} {e} {g} {s} h he =
  elimᵈ {C = λ q → e→f r2 g s ＝ af (e→f r1 g) (if ⌊ q ⌋ then e else AVar s)}
        (λ e → update-af (subst (λ q → SUpdate r1 q v r2) e h) ∙ af-correct he ⁻¹)
        (λ ¬e → update-af-diff h ¬e)
        (x ≟ s)

update-af-subst : ∀ {r1 x v r2 e' g} e
                → SUpdate r1 x v r2 → AEval r1 e' v
                → af (e→f r2 g) e ＝ af (e→f r1 g) (asubst x e' e)
update-af-subst (ANum n)      su ae = refl
update-af-subst (AVar x)      su ae = update-af-var-subst su ae
update-af-subst (APlus e₁ e₂) su ae = ap² _+_ (update-af-subst e₁ su ae) (update-af-subst e₂ su ae)

update-fp-subst-l : ∀ {r1 x v r2 e' g s} {l : List AExpr} m
                  → SUpdate r1 x v r2 → AEval r1 e' v
                  → fp m s (map (af (e→f r1 g) ∘ asubst x e') l)
                  → fp m s (map (af (e→f r2 g)) l)
update-fp-subst-l                                []             su ae tt = tt
update-fp-subst-l {r1} {x} {r2} {e'} {g} {s} {l} ((a , p1) ∷ m) su ae    =
  elimᵈ {C = λ q → if ⌊ q ⌋ then p1 (map (af (e→f r1 g) ∘ asubst x e') l)
                            else fp m s (map (af (e→f r1 g) ∘ asubst x e') l) →
                   if ⌊ q ⌋ then p1 (map (af (e→f r2 g)) l)
                            else fp m s (map (af (e→f r2 g)) l)}
        (λ e h → subst (λ q → p1 (map q l)) (fun-ext λ z → update-af-subst z su ae ⁻¹) h)
        (λ ¬e → update-fp-subst-l m su ae)
        (a ≟ s)

update-fp-subst-r : ∀ {r1 x v r2 e' g s} {l : List AExpr} m
                  → SUpdate r1 x v r2 → AEval r1 e' v
                  → fp m s (map (af (e→f r2 g)) l)
                  → fp m s (map (af (e→f r1 g) ∘ asubst x e') l)
update-fp-subst-r                                []             su ae tt = tt
update-fp-subst-r {r1} {x} {r2} {e'} {g} {s} {l} ((a , p1) ∷ m) su ae    =
    elimᵈ {C = λ q → if ⌊ q ⌋ then p1 (map (af (e→f r2 g)) l)
                            else fp m s (map (af (e→f r2 g)) l) →
                     if ⌊ q ⌋ then p1 (map (af (e→f r1 g) ∘ asubst x e') l)
                            else fp m s (map (af (e→f r1 g) ∘ asubst x e') l)}
        (λ e h → subst (λ q → p1 (map q l)) (fun-ext λ z → update-af-subst z su ae) h)
        (λ ¬e → update-fp-subst-r m su ae)
        (a ≟ s)

mutual
  subst-correct-l : ∀ {r1 e v m g r2 x} a
                  → AEval r1 e v
                  → SUpdate r1 x v r2
                  → ia m (e→f r1 g) (qsubst x e a)
                  → ia m (e→f r2 g) a
  subst-correct-l          {m}              (QPred x e)      ae su h         =
    update-fp-subst-l m su ae $
    subst (fp m x) (map-list-comp e ⁻¹) h
  subst-correct-l {r1} {e}     {g} {r2} {x} (QB (BLt a₁ a₂)) ae su h         =
    subst (λ q → is-true (q <ᵇ af (e→f r2 g) a₂)) (update-af-subst a₁ su ae ⁻¹) $
    subst (λ q → is-true (af (e→f r1 g) (asubst x e a₁) <ᵇ q)) (update-af-subst a₂ su ae ⁻¹) h
  subst-correct-l                           (QConj q₁ q₂)    ae su (h1 , h2) =
    subst-correct-l q₁ ae su h1 , subst-correct-l q₂ ae su h2
  subst-correct-l                           (QNot q)         ae su h         =
    h ∘ subst-correct-r q ae su
  subst-correct-l                            QTrue           ae su tt        = tt

  subst-correct-r : ∀ {r1 e v m g r2 x} a
                  → AEval r1 e v
                  → SUpdate r1 x v r2
                  → ia m (e→f r2 g) a
                  → ia m (e→f r1 g) (qsubst x e a)
  subst-correct-r          {m}              (QPred x e)      ae su h         =
    subst (fp m x) (map-list-comp e) $
    update-fp-subst-r m su ae h
  subst-correct-r {r1} {e}     {g} {r2} {x} (QB (BLt a₁ a₂)) ae su h         =
    subst (λ q → is-true (q <ᵇ af (e→f r1 g) (asubst x e a₂))) (update-af-subst a₁ su ae) $
    subst (λ q → is-true (af (e→f r2 g) a₁ <ᵇ q)) (update-af-subst a₂ su ae) h
  subst-correct-r                           (QConj q₁ q₂)    ae su (h1 , h2) =
    subst-correct-r q₁ ae su h1 , subst-correct-r q₂ ae su h2
  subst-correct-r                           (QNot q)         ae su h         =
    h ∘ subst-correct-l q ae su
  subst-correct-r                            QTrue           ae su tt        = tt

beval-true-interpret : ∀ {r b g}
                     → BEval r b true
                     → is-true (bf (e→f r g) b)
beval-true-interpret {r} {b} {g} (BELtT {e2} {v1} {v2} a1 a2 lt) =
  subst (λ q → is-true (q <ᵇ af (e→f r g) e2)) (af-correct a1 ⁻¹) $
  subst (λ q → is-true (v1 <ᵇ q)) (af-correct a2 ⁻¹) $
  reflects-true (<-reflects v1 v2) lt

beval-false-interpret : ∀ {r b g}
                     → BEval r b false
                     → is-true (not (bf (e→f r g) b))
beval-false-interpret {r} {b} {g} (BELtF {e2} {v1} {v2} a1 a2 le) =
  subst (λ q → is-true (not (q <ᵇ af (e→f r g) e2))) (af-correct a1 ⁻¹) $
  subst (λ q → is-true (not (v1 <ᵇ q))) (af-correct a2 ⁻¹) $
  reflects-false (<-reflects v1 v2) (≤≃≯ $ le)

nax-sound : ∀ {m r i r' g} → Exec r i r'
          → ∀ {p q} → NAx m p i q
          → ia m (e→f r g) p → ia m (e→f r' g) q
nax-sound  ExSkip               (NAxSkip v)                  h = v h
nax-sound (ExAssign ae su)      (NAxAssign {p'} v₁ v₂)       h =
  v₂ (subst-correct-l p' ae su (v₁ h))
nax-sound (ExSeq ex₁ ex₂)       (NAxSeq v₁ v₂ na₁ na₂)       h =
  v₂ (nax-sound ex₂ na₂ (nax-sound ex₁ na₁ (v₁ h)))
nax-sound (ExWhileT bt ex₁ ex₂) (NAxWhile {p'} {b} v₁ v₂ na) h =
  v₂ (nax-sound ex₂ {p = p'} {q = QConj p' (QNot (QB b))} (NAxWhile id id na) $
      nax-sound ex₁ na (v₁ h , beval-true-interpret bt))
nax-sound (ExWhileF bf)         (NAxWhile v₁ v₂ na)          h =
  v₂ (v₁ h , true-reflects reflects-not (beval-false-interpret bf))

ax-sem-sound : ∀ {m r i r' g p q}
             → Exec r i r' → AxSem m p i q
             → ia m (e→f r g) p → ia m (e→f r' g) q
ax-sem-sound ex as = nax-sound ex (ax-sem→nax as)

{- Correctness proof: the vcg -}

all-ic : PEnv → (String → ℕ) → List Cond → 𝒰
all-ic p g l = All (ic p g) l

all-ic-prop : {p : PEnv} {g : String → ℕ} {l : List Cond}
        → (All (λ sf → (l : List ℕ) → is-prop (sf .snd l)) p)
        → is-prop (all-ic p g l)
all-ic-prop {l} pp = All-is-of-hlevel 0 λ c → ic-prop {c = c} pp

all-valid : PEnv → List Cond → 𝒰
all-valid p l = ∀ {g} → all-ic p g l

all-valid-cons : {p : PEnv} {c : Cond} {l : List Cond}
               → valid p c → all-valid p l
               → all-valid p (c ∷ l)
all-valid-cons v av {g} = v ∷ av

all-valid-uncons : {p : PEnv} {c : Cond} {l : List Cond}
                 → all-valid p (c ∷ l) → valid p c × all-valid p l
all-valid-uncons av = (λ {g} → all-uncons (av {g = g}) .fst) , λ {g} → all-uncons (av {g = g}) .snd

all-valid-++ : {p : PEnv} {l1 l2 : List Cond}
             → all-valid p l1 → all-valid p l2
             → all-valid p (l1 ++ l2)
all-valid-++ av1 av2 {g} = all-++ (av1 {g = g}) (av2 {g = g})

all-valid-split : {p : PEnv} {l1 l2 : List Cond}
                 → all-valid p (l1 ++ l2) → all-valid p l1 × all-valid p l2
all-valid-split av = (λ {g} → all-++-left (av {g = g})) , λ {g} → all-++-right (av {g = g})

all-valid-prop : {p : PEnv} {l : List Cond}
               → (All (λ sf → (l : List ℕ) → is-prop (sf .snd l)) p)
               → is-prop (all-valid p l)
all-valid-prop pp = ∀-is-of-hlevel 1 λ g → all-ic-prop pp

vcg-ax : ∀ {m a} i → all-valid m (vc i a) → AxSem m (pc i a) (cleanup i) a
vcg-ax {a} (AnPre q i)     av =
  let (v1 , av1) = all-valid-uncons av in
  AxConseq {p' = pc i a} {q' = a} v1 (vcg-ax i av1) id
vcg-ax      AnSkip         av = AxSkip
vcg-ax     (AnAssign s a)  av = AxAssign
vcg-ax {a} (AnSeq i₁ i₂)   av =
  let (av1 , av2) = all-valid-split av in
  AxSeq {q = pc i₂ a} (vcg-ax i₁ av1) (vcg-ax i₂ av2)
vcg-ax     (AnWhile b q i) av =
  let (v1 , av1) = all-valid-uncons av
      (v2 , av2) = all-valid-uncons av1
    in
  AxConseq {p' = q} {q' = QConj q (QNot (QB b))} id
    (AxWhile (AxConseq {p' = pc i q} {q' = q} v1 (vcg-ax i av2) id))
    v2

vcg-sound : ∀ {ps i a g r1 r2}
          → all-valid ps (vc i a)
          → Exec r1 (cleanup i) r2
          → ia ps (e→f r1 g) (pc i a) → ia ps (e→f r2 g) a
vcg-sound {i} av ex = ax-sem-sound ex (vcg-ax i av)

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
subst-sound-l (h ∷ t) = ap² List._∷_ (subst-sound-a h) (subst-sound-l t)

subst-sound : {pe : PEnv} {g : String → ℕ} {e : AExpr} {x : String}
            → (a : Assert)
            → ia pe g (qsubst x e a) ＝ ia pe (λ y → if ⌊ x ≟ y ⌋ then af g e else g y) a
subst-sound {pe} (QPred s l)  = ap (fp pe s) (subst-sound-l l)
subst-sound     (QB b)        = ap is-true (subst-sound-b b)
subst-sound     (QConj a₁ a₂) = ap² _×_ (subst-sound a₁) (subst-sound a₂)
subst-sound     (QNot a)      = ap ¬_ (subst-sound a)
subst-sound      QTrue        = refl
subst-sound      QFalse       = refl

vc-monotonic : ∀ {pe p1 p2} → (i : AnInstr)
             → all-valid pe (vc i p1) → (∀ g → ia pe g p1 → ia pe g p2)
             → all-valid pe (vc i p2) × (∀ g → ia pe g (pc i p1) → ia pe g (pc i p2))
vc-monotonic            AnSkip        av       p12 = [] , p12
vc-monotonic           (AnPre a i)    av       p12 =
  let (h1 , h2) = all-valid-uncons av
      (ih1 , ih2) = vc-monotonic i h2 p12
    in
  (all-valid-cons (λ {g} → ih2 g ∘ h1 {g = g}) ih1) , λ g → id
vc-monotonic {p1} {p2} (AnAssign x e) av              p12 =
  [] , λ g z → transport (subst-sound p2 ⁻¹) (p12 (λ y → if ⌊ x ≟ y ⌋ then af g e else g y) (transport (subst-sound p1) z))
vc-monotonic {p1} {p2} (AnSeq i₁ i₂)  av               p12 =
  let (h1 , h2) = all-valid-split {l1 = vc i₁ (pc i₂ p1)} {l2 = vc i₂ p1} av
      (ih21 , ih22) = vc-monotonic i₂ h2 p12
      (ih11 , ih12) = vc-monotonic {p1 = pc i₂ p1} {p2 = pc i₂ p2} i₁ h1 ih22
    in
  all-valid-++ ih11 ih21 , ih12
vc-monotonic           (AnWhile b a i) av {-(v12 , vn , vc)-} p12 =
  let (h1 , av1) = all-valid-uncons av
      (h2 , h3) = all-valid-uncons av1
    in
  all-valid-cons h1 (all-valid-cons (λ {g} → p12 g ∘ h2 {g = g}) h3) , (λ g → id)
