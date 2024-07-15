module Nipkow.Lang where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming (_==_ to _==ᵇ_)
open import Data.Nat renaming (_==_ to _==ⁿ_)
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects renaming (dmap to dmapʳ)

open import List1

private variable
  A : 𝒰

{- The programming language -}

data AExpr : 𝒰 where
  ANum  : ℕ → AExpr
  AVar  : String → AExpr
  APlus : AExpr → AExpr → AExpr

module AExprCode where
  Code-aexpr : AExpr → AExpr → 𝒰
  Code-aexpr (ANum n)      (ANum m)      = n ＝ m
  Code-aexpr (AVar x)      (AVar y)      = x ＝ y
  Code-aexpr (APlus a₁ a₂) (APlus a₃ a₄) = Code-aexpr a₁ a₃ × Code-aexpr a₂ a₄
  Code-aexpr _              _            = ⊥

  code-aexpr-refl : (a : AExpr) → Code-aexpr a a
  code-aexpr-refl (ANum n)      = refl
  code-aexpr-refl (AVar x)      = refl
  code-aexpr-refl (APlus a₁ a₂) = code-aexpr-refl a₁ , code-aexpr-refl a₂

  encode-aexpr : ∀ {a₁ a₂} → a₁ ＝ a₂ → Code-aexpr a₁ a₂
  encode-aexpr {a₁} e = subst (Code-aexpr a₁) e (code-aexpr-refl a₁)

  decode-aexpr : ∀ {a₁ a₂} → Code-aexpr a₁ a₂ → a₁ ＝ a₂
  decode-aexpr {ANum n}      {ANum m}       c        = ap ANum c
  decode-aexpr {AVar x}      {AVar y}       c        = ap AVar c
  decode-aexpr {APlus a₁ a₂} {APlus a₃ a₄} (c₁ , c₂) = ap² APlus (decode-aexpr c₁) (decode-aexpr c₂)

ANum-inj : ∀ {n m} → ANum n ＝ ANum m → n ＝ m
ANum-inj = AExprCode.encode-aexpr

AVar-inj : ∀ {x y} → AVar x ＝ AVar y → x ＝ y
AVar-inj = AExprCode.encode-aexpr

APlus-inj : ∀ {a₁ a₂ a₃ a₄} → APlus a₁ a₂ ＝ APlus a₃ a₄ → (a₁ ＝ a₃) × (a₂ ＝ a₄)
APlus-inj e = let (c₁ , c₂) = AExprCode.encode-aexpr e in AExprCode.decode-aexpr c₁ , AExprCode.decode-aexpr c₂

ANum≠AVar : ∀ {n y} → ANum n ≠ AVar y
ANum≠AVar = AExprCode.encode-aexpr

AVar≠ANum : ∀ {x m} → AVar x ≠ ANum m
AVar≠ANum = AExprCode.encode-aexpr

ANum≠APlus : ∀ {n a₁ a₂} → ANum n ≠ APlus a₁ a₂
ANum≠APlus = AExprCode.encode-aexpr

AVar≠APlus : ∀ {x a₁ a₂} → AVar x ≠ APlus a₁ a₂
AVar≠APlus = AExprCode.encode-aexpr

APlus≠ANum : ∀ {a₁ a₂ m} → APlus a₁ a₂ ≠ ANum m
APlus≠ANum = AExprCode.encode-aexpr

APlus≠AVar : ∀ {a₁ a₂ y} → APlus a₁ a₂ ≠ AVar y
APlus≠AVar = AExprCode.encode-aexpr

_==ᵃᵉ_ : AExpr → AExpr → Bool
(ANum n)      ==ᵃᵉ (ANum m)      = n ==ⁿ m
(AVar x)      ==ᵃᵉ (AVar y)      = ⌊ x ≟ y ⌋
(APlus e₁ e₂) ==ᵃᵉ (APlus e₃ e₄) = e₁ ==ᵃᵉ e₃ and e₂ ==ᵃᵉ e₄
_             ==ᵃᵉ _             = false

reflects-aexpr : ∀ a₁ a₂ → Reflects (a₁ ＝ a₂) (a₁ ==ᵃᵉ a₂)
reflects-aexpr (ANum n)      (ANum m)      = dmapʳ (ap ANum) (λ c → c ∘ ANum-inj) (==-reflects n m)
reflects-aexpr (ANum n)      (AVar y)      = ofⁿ ANum≠AVar
reflects-aexpr (ANum n)      (APlus a₃ a₄) = ofⁿ ANum≠APlus
reflects-aexpr (AVar x)      (ANum m)      = ofⁿ AVar≠ANum
reflects-aexpr (AVar x)      (AVar y)      = dmapʳ (ap AVar) (λ c → c ∘ AVar-inj) (discrete-reflects! {x = x} {y = y})
reflects-aexpr (AVar x)      (APlus a₃ a₄) = ofⁿ AVar≠APlus
reflects-aexpr (APlus a₁ a₂) (ANum m)      = ofⁿ APlus≠ANum
reflects-aexpr (APlus a₁ a₂) (AVar y)      = ofⁿ APlus≠AVar
reflects-aexpr (APlus a₁ a₂) (APlus a₃ a₄) =
  let r₁₃ = reflects-aexpr a₁ a₃
      r₂₄ = reflects-aexpr a₂ a₄
    in
  dmapʳ (λ x → ap² APlus (true-reflects r₁₃ (x .fst)) (true-reflects r₂₄ (x .snd)))
        (λ c → c ∘ (λ b → (reflects-true r₁₃ (b .fst)) , reflects-true r₂₄ (b .snd)) ∘ APlus-inj)
        reflects-and

af : (String → ℕ) → AExpr → ℕ
af g (ANum n)      = n
af g (AVar x)      = g x
af g (APlus e₁ e₂) = af g e₁ + af g e₂

data BExpr : 𝒰 where
  BC   : Bool → BExpr
  BNot : BExpr → BExpr
  BAnd : BExpr → BExpr → BExpr
  BLt  : AExpr → AExpr → BExpr

module BExprCode where
  Code-bexpr : BExpr → BExpr → 𝒰
  Code-bexpr (BC c₁)      (BC c₂)      = c₁ ＝ c₂
  Code-bexpr (BNot b₁)    (BNot b₂)    = Code-bexpr b₁ b₂
  Code-bexpr (BAnd b₁ b₂) (BAnd b₃ b₄) = Code-bexpr b₁ b₃ × Code-bexpr b₂ b₄
  Code-bexpr (BLt a₁ a₂)  (BLt a₃ a₄)  = (a₁ ＝ a₃) × (a₂ ＝ a₄)
  Code-bexpr _            _            = ⊥

  code-bexpr-refl : (b : BExpr) → Code-bexpr b b
  code-bexpr-refl (BC c)       = refl
  code-bexpr-refl (BNot b)     = code-bexpr-refl b
  code-bexpr-refl (BAnd b₁ b₂) = code-bexpr-refl b₁ , code-bexpr-refl b₂
  code-bexpr-refl (BLt a₁ a₂)  = refl , refl

  encode-bexpr : ∀ {b₁ b₂} → b₁ ＝ b₂ → Code-bexpr b₁ b₂
  encode-bexpr {b₁} e = subst (Code-bexpr b₁) e (code-bexpr-refl b₁)

  decode-bexpr : ∀ {b₁ b₂} → Code-bexpr b₁ b₂ → b₁ ＝ b₂
  decode-bexpr {BC c₁}      {BC c₂}       c        = ap BC c
  decode-bexpr {BNot b₁}    {BNot b₂}     c        = ap BNot (decode-bexpr c)
  decode-bexpr {BAnd b₁ b₂} {BAnd b₃ b₄} (c₁ , c₂) = ap² BAnd (decode-bexpr c₁) (decode-bexpr c₂)
  decode-bexpr {BLt a₁ a₂}  {BLt a₃ a₄}  (c₁ , c₂) = ap² BLt c₁ c₂

bf : (String → ℕ) → BExpr → Bool
bf g (BC c)       = c
bf g (BNot b)     = not (bf g b)
bf g (BAnd b₁ b₂) = bf g b₁ and bf g b₂
bf g (BLt e₁ e₂)  = af g e₁ <ᵇ af g e₂

_==ᵇᵉ_ : BExpr → BExpr → Bool
(BC c₁)      ==ᵇᵉ (BC c₂)      = c₁ ==ᵇ c₂
(BNot e₁)    ==ᵇᵉ (BNot e₂)    = e₁ ==ᵇᵉ e₂
(BAnd e₁ e₂) ==ᵇᵉ (BAnd e₃ e₄) = e₁ ==ᵇᵉ e₃ and e₂ ==ᵇᵉ e₄
(BLt e₁ e₂)  ==ᵇᵉ (BLt e₃ e₄)  = e₁ ==ᵃᵉ e₃ and e₂ ==ᵃᵉ e₄
_            ==ᵇᵉ _            = false

data Instr : 𝒰 where
  Skip   : Instr
  Assign : String → AExpr → Instr
  Seq    : Instr → Instr → Instr
  ITE    : BExpr → Instr → Instr → Instr
  While  : BExpr → Instr → Instr

_==ⁱ_ : Instr → Instr → Bool
Skip           ==ⁱ Skip           = true
(Assign x e₁)  ==ⁱ (Assign y e₂)  = ⌊ x ≟ y ⌋ and e₁ ==ᵃᵉ e₂
(Seq x₁ x₂)    ==ⁱ (Seq y₁ y₂)    = x₁ ==ⁱ y₁ and x₂ ==ⁱ y₂
(ITE b₁ x₁ x₂) ==ⁱ (ITE b₂ y₁ y₂) = b₁ ==ᵇᵉ b₂ and x₁ ==ⁱ y₁ and x₂ ==ⁱ y₂
(While b₁ x₁)  ==ⁱ (While b₂ x₂)  = b₁ ==ᵇᵉ b₂ and x₁ ==ⁱ x₂
_              ==ⁱ _              = false

{- Annotated commands -}

data AnInstr (A : 𝒰) : 𝒰 where
  AnSkip   : (p : A) → AnInstr A
  AnAssign : (x : String) → (e : AExpr) → (p : A) → AnInstr A
  AnSeq    : (c₁ : AnInstr A) → (c₂ : AnInstr A) → AnInstr A
  AnITE    : (b : BExpr) → (p₁ : A) → (c₁ : AnInstr A) → (p₂ : A) → (c₂ : AnInstr A) → (q : A) → AnInstr A
  AnWhile  : (inv : A) → (b : BExpr) → (p : A)  → (c : AnInstr A) → (q : A) → AnInstr A

module AnInstrCode where
  Code-AnInstr : AnInstr A → AnInstr A → 𝒰
  Code-AnInstr (AnSkip p₁)                (AnSkip p₂)                = p₁ ＝ p₂
  Code-AnInstr (AnAssign x₁ e₁ p₁)        (AnAssign x₂ e₂ p₂)        = (x₁ ＝ x₂) × (e₁ ＝ e₂) × (p₁ ＝ p₂)
  Code-AnInstr (AnSeq c₁ c₂)              (AnSeq c₃ c₄)              = Code-AnInstr c₁ c₃ × Code-AnInstr c₂ c₄
  Code-AnInstr (AnITE b₁ p₁ c₁ p₂ c₂ q₁)  (AnITE b₂ p₃ c₃ p₄ c₄ q₂)  =
    (b₁ ＝ b₂) × (p₁ ＝ p₃) × Code-AnInstr c₁ c₃ × (p₂ ＝ p₄) × Code-AnInstr c₂ c₄ × (q₁ ＝ q₂)
  Code-AnInstr (AnWhile inv₁ b₁ p₁ c₁ q₁) (AnWhile inv₂ b₂ p₂ c₂ q₂) =
    (inv₁ ＝ inv₂) × (b₁ ＝ b₂) × (p₁ ＝ p₂) × Code-AnInstr c₁ c₂ × (q₁ ＝ q₂)
  Code-AnInstr _                           _                         = ⊥

  code-aninstr-refl : (c : AnInstr A) → Code-AnInstr c c
  code-aninstr-refl (AnSkip p)              = refl
  code-aninstr-refl (AnAssign x e p)        = refl , refl , refl
  code-aninstr-refl (AnSeq c₁ c₂)           = code-aninstr-refl c₁ , code-aninstr-refl c₂
  code-aninstr-refl (AnITE b p₁ c₁ p₂ c₂ q) = refl , refl , code-aninstr-refl c₁ , refl , code-aninstr-refl c₂ , refl
  code-aninstr-refl (AnWhile inv b p c q)   = refl , refl , refl , code-aninstr-refl c , refl

  encode-aninstr : ∀ {c₁ c₂ : AnInstr A} → c₁ ＝ c₂ → Code-AnInstr c₁ c₂
  encode-aninstr {c₁} e = subst (Code-AnInstr c₁) e (code-aninstr-refl c₁)

  decode-aninstr : ∀ {c₁ c₂ : AnInstr A} → Code-AnInstr c₁ c₂ → c₁ ＝ c₂
  decode-aninstr {c₁ = AnSkip p₁}                {AnSkip p₂}                 cd                                 = ap AnSkip cd
  decode-aninstr {c₁ = AnAssign x₁ e₁ p₁}        {AnAssign x₂ e₂ p₂}        (cd₁ , cd₂ , cd₃)                   =
    ap (λ q → AnAssign q e₁ p₁) cd₁ ∙ ap² (AnAssign x₂) cd₂ cd₃
  decode-aninstr {c₁ = AnSeq c₁ c₂}              {AnSeq c₃ c₄}              (cd₁ , cd₂)                         =
    ap² AnSeq (decode-aninstr cd₁) (decode-aninstr cd₂)
  decode-aninstr {c₁ = AnITE b₁ p₁ c₁ p₂ c₂ q₁}  {AnITE b₂ p₃ c₃ p₄ c₄ q₂}  (cd₁ , cd₂ , cd₃ , cd₄ , cd₅ , cd₆) =
    ap² (λ z₁ z₂ → AnITE z₁ z₂ c₁ p₂ c₂ q₁) cd₁ cd₂
    ∙ ap² (λ z₁ z₂ → AnITE b₂ p₃ z₁ z₂ c₂ q₁) (decode-aninstr cd₃) cd₄
    ∙ ap² (AnITE b₂ p₃ c₃ p₄) (decode-aninstr cd₅) cd₆
  decode-aninstr {c₁ = AnWhile inv₁ b₁ p₁ c₁ q₁} {AnWhile inv₂ b₂ p₂ c₂ q₂} (cd₁ , cd₂ , cd₃ , cd₄ , cd₅)       =
    ap (λ z → AnWhile z b₁ p₁ c₁ q₁) cd₁
    ∙ ap² (λ z₁ z₂ → AnWhile inv₂ z₁ z₂ c₁ q₁) cd₂ cd₃
    ∙ ap² (AnWhile inv₂ b₂ p₂) (decode-aninstr cd₄) cd₅

AnSkip-inj : ∀ {p₁ p₂ : A} → AnSkip p₁ ＝ AnSkip p₂ → p₁ ＝ p₂
AnSkip-inj = AnInstrCode.encode-aninstr

AnSkip≠AnAssign : ∀ {x e} {p q : A} → AnSkip p ≠ AnAssign x e q
AnSkip≠AnAssign = AnInstrCode.encode-aninstr

AnAssign≠AnSkip : ∀ {x e} {p q : A} → AnAssign x e p ≠ AnSkip q
AnAssign≠AnSkip = AnInstrCode.encode-aninstr

AnSeq≠AnSkip : ∀ {c₁ c₂} {q : A} → AnSeq c₁ c₂ ≠ AnSkip q
AnSeq≠AnSkip = AnInstrCode.encode-aninstr

AnSeq≠AnAssign : ∀ {x e c₁ c₂} {p : A} → AnSeq c₁ c₂ ≠ AnAssign x e p
AnSeq≠AnAssign = AnInstrCode.encode-aninstr

AnITE≠AnSkip : ∀ {b c₁ c₂} {p₁ p₂ q r : A} → AnITE b p₁ c₁ p₂ c₂ q ≠ AnSkip r
AnITE≠AnSkip = AnInstrCode.encode-aninstr

AnITE≠AnAssign : ∀ {b c₁ c₂ x e} {p₁ p₂ q r : A} → AnITE b p₁ c₁ p₂ c₂ q ≠ AnAssign x e r
AnITE≠AnAssign = AnInstrCode.encode-aninstr

AnWhile≠AnSkip : ∀ {b c} {inv p q r : A} → AnWhile inv b p c q ≠ AnSkip r
AnWhile≠AnSkip = AnInstrCode.encode-aninstr

AnWhile≠AnAssign : ∀ {b c x e} {inv p q r : A} → AnWhile inv b p c q ≠ AnAssign x e r
AnWhile≠AnAssign = AnInstrCode.encode-aninstr

annos : AnInstr A → List1 A
annos (AnSkip p)              = [ p ]₁
annos (AnAssign _ _ p)        = [ p ]₁
annos (AnSeq c₁ c₂)           = annos c₁ ++₁ annos c₂
annos (AnITE b p₁ c₁ p₂ c₂ q) = to-list ((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) +∶ q
annos (AnWhile inv b p c q)   = to-list (inv ∷₁ (q ∷₁ annos c)) +∶ q

post : AnInstr A → A
post = List1.last ∘ annos

strip : AnInstr A → Instr
strip (AnSkip _)            = Skip
strip (AnAssign x e _)      = Assign x e
strip (AnSeq c₁ c₂)         = Seq (strip c₁) (strip c₂)
strip (AnITE b _ c₁ _ c₂ _) = ITE b (strip c₁) (strip c₂)
strip (AnWhile _ b _ c _)   = While b (strip c)
