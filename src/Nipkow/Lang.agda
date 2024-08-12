module Nipkow.Lang where

open import Prelude
open import Data.Empty
open import Data.Bool renaming (_==_ to _==ᵇ_ ; ==-reflects to ==ᵇ-reflects)
open import Data.Nat renaming (_==_ to _==ⁿ_ ; ==-reflects to ==ⁿ-reflects)
open import Data.Nat.Order.Base
open import Data.Sum
open import Data.String
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects renaming (dmap to dmapʳ)

open import Nipkow.State as S

{- The programming language -}

{- Arithmetic expressions -}

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

  code-aexpr-is-prop : ∀ a b → is-prop (Code-aexpr a b)
  code-aexpr-is-prop (ANum n₁)     (ANum n₂)     = hlevel!
  code-aexpr-is-prop (ANum n₁)     (AVar x₂)     = hlevel!
  code-aexpr-is-prop (ANum n₁)     (APlus b₁ b₂) = hlevel!
  code-aexpr-is-prop (AVar x₁)     (ANum n₂)     = hlevel!
  code-aexpr-is-prop (AVar x₁)     (AVar x₂)     = path-is-of-hlevel 1 (is-discrete→is-set string-is-discrete) x₁ x₂
  code-aexpr-is-prop (AVar x₁)     (APlus b₁ b₂) = hlevel!
  code-aexpr-is-prop (APlus a₁ a₂) (ANum n₂)     = hlevel!
  code-aexpr-is-prop (APlus a₁ a₂) (AVar x₂)     = hlevel!
  code-aexpr-is-prop (APlus a₁ a₂) (APlus b₁ b₂) = ×-is-of-hlevel 1 (code-aexpr-is-prop a₁ b₁) (code-aexpr-is-prop a₂ b₂)

  AExpr-identity-system : is-identity-system Code-aexpr code-aexpr-refl
  AExpr-identity-system = set-identity-system code-aexpr-is-prop decode-aexpr

instance
  H-Level-AExpr : ∀ {n} → H-Level (2 + n) AExpr
  H-Level-AExpr = hlevel-basic-instance 2 $
                  identity-system→is-of-hlevel 1
                    AExprCode.AExpr-identity-system
                    AExprCode.code-aexpr-is-prop
  {-# OVERLAPPING H-Level-AExpr #-}

ANum-inj : ∀ {n m} → ANum n ＝ ANum m → n ＝ m
ANum-inj = AExprCode.encode-aexpr

AVar-inj : ∀ {x y} → AVar x ＝ AVar y → x ＝ y
AVar-inj = AExprCode.encode-aexpr

APlus-inj : ∀ {a₁ a₂ a₃ a₄} → APlus a₁ a₂ ＝ APlus a₃ a₄ → (a₁ ＝ a₃) × (a₂ ＝ a₄)
APlus-inj e = let (c₁ , c₂) = AExprCode.encode-aexpr e in AExprCode.decode-aexpr c₁ , AExprCode.decode-aexpr c₂

ANum≠AVar : ∀ {n y} → ANum n ≠ AVar y
ANum≠AVar = AExprCode.encode-aexpr

ANum≠APlus : ∀ {n a₁ a₂} → ANum n ≠ APlus a₁ a₂
ANum≠APlus = AExprCode.encode-aexpr

AVar≠APlus : ∀ {x a₁ a₂} → AVar x ≠ APlus a₁ a₂
AVar≠APlus = AExprCode.encode-aexpr

_==ᵃᵉ_ : AExpr → AExpr → Bool
(ANum n)      ==ᵃᵉ (ANum m)      = n ==ⁿ m
(AVar x)      ==ᵃᵉ (AVar y)      = ⌊ x ≟ y ⌋
(APlus e₁ e₂) ==ᵃᵉ (APlus e₃ e₄) = e₁ ==ᵃᵉ e₃ and e₂ ==ᵃᵉ e₄
_             ==ᵃᵉ _             = false

reflects-aexpr : ∀ a₁ a₂ → Reflects (a₁ ＝ a₂) (a₁ ==ᵃᵉ a₂)
reflects-aexpr (ANum n)      (ANum m)      = dmapʳ (ap ANum) (_∘ ANum-inj) (==ⁿ-reflects n m)
reflects-aexpr (ANum n)      (AVar y)      = ofⁿ ANum≠AVar
reflects-aexpr (ANum n)      (APlus a₃ a₄) = ofⁿ ANum≠APlus
reflects-aexpr (AVar x)      (ANum m)      = ofⁿ (ANum≠AVar ∘ _⁻¹)
reflects-aexpr (AVar x)      (AVar y)      = dmapʳ (ap AVar) (_∘ AVar-inj) (discrete-reflects! {x = x} {y = y})
reflects-aexpr (AVar x)      (APlus a₃ a₄) = ofⁿ AVar≠APlus
reflects-aexpr (APlus a₁ a₂) (ANum m)      = ofⁿ (ANum≠APlus ∘ _⁻¹)
reflects-aexpr (APlus a₁ a₂) (AVar y)      = ofⁿ (AVar≠APlus ∘ _⁻¹)
reflects-aexpr (APlus a₁ a₂) (APlus a₃ a₄) =
  dmapʳ (λ x → ap² APlus (x .fst) (x .snd)) (_∘ APlus-inj)
        (reflects-× (reflects-aexpr a₁ a₃) (reflects-aexpr a₂ a₄))

open S.State ℕ 0

aval : State → AExpr → ℕ
aval s (ANum n)      = n
aval s (AVar x)      = stlup s x
aval s (APlus e₁ e₂) = aval s e₁ + aval s e₂

{- Boolean expressions -}

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

  code-bexpr-is-prop : ∀ a b → is-prop (Code-bexpr a b)
  code-bexpr-is-prop (BC x)       (BC y)       = hlevel!
  code-bexpr-is-prop (BC x)       (BNot b)     = hlevel!
  code-bexpr-is-prop (BC x)       (BAnd b₁ b₂) = hlevel!
  code-bexpr-is-prop (BC x)       (BLt b₁ b₂)  = hlevel!
  code-bexpr-is-prop (BNot a)     (BC x)       = hlevel!
  code-bexpr-is-prop (BNot a)     (BNot b)     = code-bexpr-is-prop a b
  code-bexpr-is-prop (BNot a)     (BAnd b₁ b₂) = hlevel!
  code-bexpr-is-prop (BNot a)     (BLt x x₁)   = hlevel!
  code-bexpr-is-prop (BAnd a₁ a₂) (BC x)       = hlevel!
  code-bexpr-is-prop (BAnd a₁ a₂) (BNot b)     = hlevel!
  code-bexpr-is-prop (BAnd a₁ a₂) (BAnd b₁ b₂) = ×-is-of-hlevel 1 (code-bexpr-is-prop a₁ b₁) (code-bexpr-is-prop a₂ b₂)
  code-bexpr-is-prop (BAnd a₁ a₂) (BLt b₁ b₂)  = hlevel!
  code-bexpr-is-prop (BLt a₁ a₂)  (BC x₂)      = hlevel!
  code-bexpr-is-prop (BLt a₁ a₂)  (BNot b)     = hlevel!
  code-bexpr-is-prop (BLt a₁ a₂)  (BAnd b₁ b₂) = hlevel!
  code-bexpr-is-prop (BLt a₁ a₂)  (BLt b₁ b₂)  = hlevel!

  BExpr-identity-system : is-identity-system Code-bexpr code-bexpr-refl
  BExpr-identity-system = set-identity-system code-bexpr-is-prop decode-bexpr

instance
  H-Level-BExpr : ∀ {n} → H-Level (2 + n) BExpr
  H-Level-BExpr = hlevel-basic-instance 2 $
                  identity-system→is-of-hlevel 1
                    BExprCode.BExpr-identity-system
                    BExprCode.code-bexpr-is-prop
  {-# OVERLAPPING H-Level-BExpr #-}

BC-inj : ∀ {c₁ c₂} → BC c₁ ＝ BC c₂ → c₁ ＝ c₂
BC-inj = BExprCode.encode-bexpr

BNot-inj : ∀ {b₁ b₂} → BNot b₁ ＝ BNot b₂ → b₁ ＝ b₂
BNot-inj = BExprCode.decode-bexpr ∘ BExprCode.encode-bexpr

BAnd-inj : ∀ {b₁ b₂ b₃ b₄} → BAnd b₁ b₂ ＝ BAnd b₃ b₄ → (b₁ ＝ b₃) × (b₂ ＝ b₄)
BAnd-inj e = let (h1 , h2) = BExprCode.encode-bexpr e in
             BExprCode.decode-bexpr h1 , BExprCode.decode-bexpr h2

BLt-inj : ∀ {b₁ b₂ b₃ b₄} → BLt b₁ b₂ ＝ BLt b₃ b₄ → (b₁ ＝ b₃) × (b₂ ＝ b₄)
BLt-inj = BExprCode.encode-bexpr

BC≠BNot : ∀ {c e} → BC c ≠ BNot e
BC≠BNot = BExprCode.encode-bexpr

BC≠BAnd : ∀ {c b₁ b₂} → BC c ≠ BAnd b₁ b₂
BC≠BAnd = BExprCode.encode-bexpr

BC≠BLt : ∀ {c a₁ a₂} → BC c ≠ BLt a₁ a₂
BC≠BLt = BExprCode.encode-bexpr

BNot≠BAnd : ∀ {b₁ b₂ b₃} → BNot b₁ ≠ BAnd b₂ b₃
BNot≠BAnd = BExprCode.encode-bexpr

BNot≠BLt : ∀ {b a₁ a₂} → BNot b ≠ BLt a₁ a₂
BNot≠BLt = BExprCode.encode-bexpr

BAnd≠BLt : ∀ {b₁ b₂ a₁ a₂} → BAnd b₁ b₂ ≠ BLt a₁ a₂
BAnd≠BLt = BExprCode.encode-bexpr

_==ᵇᵉ_ : BExpr → BExpr → Bool
(BC c₁)      ==ᵇᵉ (BC c₂)      = c₁ ==ᵇ c₂
(BNot e₁)    ==ᵇᵉ (BNot e₂)    = e₁ ==ᵇᵉ e₂
(BAnd e₁ e₂) ==ᵇᵉ (BAnd e₃ e₄) = e₁ ==ᵇᵉ e₃ and e₂ ==ᵇᵉ e₄
(BLt e₁ e₂)  ==ᵇᵉ (BLt e₃ e₄)  = e₁ ==ᵃᵉ e₃ and e₂ ==ᵃᵉ e₄
_            ==ᵇᵉ _            = false

reflects-bexpr : ∀ b₁ b₂ → Reflects (b₁ ＝ b₂) (b₁ ==ᵇᵉ b₂)
reflects-bexpr (BC c₁)      (BC c₂)      = dmapʳ (ap BC) (_∘ BC-inj) (==ᵇ-reflects c₁ c₂)
reflects-bexpr (BC c₁)      (BNot e₂)    = ofⁿ BC≠BNot
reflects-bexpr (BC c₁)      (BAnd e₃ e₄) = ofⁿ BC≠BAnd
reflects-bexpr (BC c₁)      (BLt e₃ e₄)  = ofⁿ BC≠BLt
reflects-bexpr (BNot e₁)    (BC c₂)      = ofⁿ (BC≠BNot ∘ _⁻¹)
reflects-bexpr (BNot e₁)    (BNot e₂)    = dmapʳ (ap BNot) (_∘ BNot-inj) (reflects-bexpr e₁ e₂)
reflects-bexpr (BNot e₁)    (BAnd e₃ e₄) = ofⁿ BNot≠BAnd
reflects-bexpr (BNot e₁)    (BLt e₃ e₄)  = ofⁿ BNot≠BLt
reflects-bexpr (BAnd e₁ e₂) (BC c₂)      = ofⁿ (BC≠BAnd ∘ _⁻¹)
reflects-bexpr (BAnd e₁ e₂) (BNot e₃)    = ofⁿ (BNot≠BAnd ∘ _⁻¹)
reflects-bexpr (BAnd e₁ e₂) (BAnd e₃ e₄) =
  dmapʳ (λ x → ap² BAnd (x .fst) (x .snd)) (_∘ BAnd-inj)
        (reflects-× (reflects-bexpr e₁ e₃) (reflects-bexpr e₂ e₄))
reflects-bexpr (BAnd e₁ e₂) (BLt e₃ e₄)  = ofⁿ BAnd≠BLt
reflects-bexpr (BLt e₁ e₂)  (BC c₂)      = ofⁿ (BC≠BLt ∘ _⁻¹)
reflects-bexpr (BLt e₁ e₂)  (BNot e₃)    = ofⁿ (BNot≠BLt ∘ _⁻¹)
reflects-bexpr (BLt e₁ e₂)  (BAnd e₃ e₄) = ofⁿ (BAnd≠BLt ∘ _⁻¹)
reflects-bexpr (BLt e₁ e₂)  (BLt e₃ e₄)  =
  dmapʳ (λ x → ap² BLt (x .fst) (x .snd)) (_∘ BLt-inj)
        (reflects-× (reflects-aexpr e₁ e₃) (reflects-aexpr e₂ e₄))

bval : State → BExpr → Bool
bval s (BC c)       = c
bval s (BNot b)     = not (bval s b)
bval s (BAnd b₁ b₂) = bval s b₁ and bval s b₂
bval s (BLt e₁ e₂)  = aval s e₁ <? aval s e₂

{- Commands -}

data Instr : 𝒰 where
  Skip   : Instr
  Assign : String → AExpr → Instr
  Seq    : Instr → Instr → Instr
  ITE    : BExpr → Instr → Instr → Instr
  While  : BExpr → Instr → Instr

module InstrCode where
  Code-Instr : Instr → Instr → 𝒰
  Code-Instr  Skip           Skip          = ⊤
  Code-Instr (Assign x₁ e₁) (Assign x₂ e₂) = (x₁ ＝ x₂) × (e₁ ＝ e₂)
  Code-Instr (Seq c₁ c₂)    (Seq c₃ c₄)    = Code-Instr c₁ c₃ × Code-Instr c₂ c₄
  Code-Instr (ITE b₁ c₁ c₂) (ITE b₂ c₃ c₄) = (b₁ ＝ b₂) × Code-Instr c₁ c₃ × Code-Instr c₂ c₄
  Code-Instr (While b₁ c₁)  (While b₂ c₂)  = (b₁ ＝ b₂) × Code-Instr c₁ c₂
  Code-Instr _                           _ = ⊥

  code-instr-refl : (c : Instr) → Code-Instr c c
  code-instr-refl  Skip         = tt
  code-instr-refl (Assign x e)  = refl , refl
  code-instr-refl (Seq c₁ c₂)   = code-instr-refl c₁ , code-instr-refl c₂
  code-instr-refl (ITE b c₁ c₂) = refl , code-instr-refl c₁ , code-instr-refl c₂
  code-instr-refl (While b c)   = refl , code-instr-refl c

  encode-instr : ∀ {c₁ c₂ : Instr} → c₁ ＝ c₂ → Code-Instr c₁ c₂
  encode-instr {c₁} e = subst (Code-Instr c₁) e (code-instr-refl c₁)

  decode-instr : ∀ {c₁ c₂ : Instr} → Code-Instr c₁ c₂ → c₁ ＝ c₂
  decode-instr {c₁ = Skip}          {c₂ = Skip}           cd               = refl
  decode-instr {c₁ = Assign x₁ e₁}  {c₂ = Assign x₂ e₂}  (cd₁ , cd₂)       = ap² Assign cd₁ cd₂
  decode-instr {c₁ = Seq c₁ c₂}     {c₂ = Seq c₃ c₄}     (cd₁ , cd₂)       =
    ap² Seq (decode-instr cd₁) (decode-instr cd₂)
  decode-instr {c₁ = ITE b₁ c₁ c₂}  {c₂ = ITE b₂ c₃ c₄}  (cd₁ , cd₂ , cd₃) =
      ap (λ z → ITE z c₁ c₂) cd₁
    ∙ ap² (ITE b₂) (decode-instr cd₂) (decode-instr cd₃)
  decode-instr {c₁ = While b₁ c₁}   {c₂ = While b₂ c₂}   (cd₁ , cd₂)       =
    ap² While cd₁ (decode-instr cd₂)

Assign-inj : ∀ {x e y g} → Assign x e ＝ Assign y g → (x ＝ y) × (e ＝ g)
Assign-inj = InstrCode.encode-instr

Seq-inj : ∀ {c₁ c₂ c₃ c₄} → Seq c₁ c₂ ＝ Seq c₃ c₄ → (c₁ ＝ c₃) × (c₂ ＝ c₄)
Seq-inj e = let (h1 , h2) = InstrCode.encode-instr e in
            InstrCode.decode-instr h1 , InstrCode.decode-instr h2

ITE-inj : ∀ {b₁ b₂ c₁ c₂ c₃ c₄} → ITE b₁ c₁ c₂ ＝ ITE b₂ c₃ c₄ → (b₁ ＝ b₂) × (c₁ ＝ c₃) × (c₂ ＝ c₄)
ITE-inj e = let (h1 , h2 , h3) = InstrCode.encode-instr e in
            h1 , InstrCode.decode-instr h2 , InstrCode.decode-instr h3

While-inj : ∀ {b₁ b₂ c₁ c₂} → While b₁ c₁ ＝ While b₂ c₂ → (b₁ ＝ b₂) × (c₁ ＝ c₂)
While-inj e = let (h1 , h2) = InstrCode.encode-instr e in
              h1 , InstrCode.decode-instr h2

Skip≠Assign : ∀ {x e} → Skip ≠ Assign x e
Skip≠Assign = InstrCode.encode-instr

Skip≠Seq : ∀ {c₁ c₂} → Skip ≠ Seq c₁ c₂
Skip≠Seq = InstrCode.encode-instr

Skip≠ITE : ∀ {b c₁ c₂} → Skip ≠ ITE b c₁ c₂
Skip≠ITE = InstrCode.encode-instr

Skip≠While : ∀ {b c} → Skip ≠ While b c
Skip≠While = InstrCode.encode-instr

Assign≠Seq : ∀ {x e c₁ c₂} → Assign x e ≠ Seq c₁ c₂
Assign≠Seq = InstrCode.encode-instr

Assign≠ITE : ∀ {b c₁ c₂ x e} → Assign x e ≠ ITE b c₁ c₂
Assign≠ITE = InstrCode.encode-instr

Assign≠While : ∀ {b c x e} → Assign x e ≠ While b c
Assign≠While = InstrCode.encode-instr

Seq≠ITE : ∀ {b c₁ c₂ c₃ c₄} → Seq c₁ c₂ ≠ ITE b c₃ c₄
Seq≠ITE = InstrCode.encode-instr

Seq≠While : ∀ {b c₁ c₂ c} → Seq c₁ c₂ ≠ While b c
Seq≠While = InstrCode.encode-instr

ITE≠While : ∀ {b₁ c₁ c₂ b₂ c₃} → ITE b₁ c₁ c₂  ≠ While b₂ c₃
ITE≠While = InstrCode.encode-instr

_==ⁱ_ : Instr → Instr → Bool
Skip           ==ⁱ Skip           = true
(Assign x e₁)  ==ⁱ (Assign y e₂)  = ⌊ x ≟ y ⌋ and e₁ ==ᵃᵉ e₂
(Seq x₁ x₂)    ==ⁱ (Seq y₁ y₂)    = x₁ ==ⁱ y₁ and x₂ ==ⁱ y₂
(ITE b₁ x₁ x₂) ==ⁱ (ITE b₂ y₁ y₂) = b₁ ==ᵇᵉ b₂ and x₁ ==ⁱ y₁ and x₂ ==ⁱ y₂
(While b₁ x₁)  ==ⁱ (While b₂ x₂)  = b₁ ==ᵇᵉ b₂ and x₁ ==ⁱ x₂
_              ==ⁱ _              = false

reflects-instr : ∀ c₁ c₂ → Reflects (c₁ ＝ c₂) (c₁ ==ⁱ c₂)
reflects-instr  Skip           Skip          = ofʸ refl
reflects-instr  Skip          (Assign _ _)   = ofⁿ Skip≠Assign
reflects-instr  Skip          (Seq _ _)      = ofⁿ Skip≠Seq
reflects-instr  Skip          (ITE _ _ _)    = ofⁿ Skip≠ITE
reflects-instr  Skip          (While _ _)    = ofⁿ Skip≠While
reflects-instr (Assign _ _)    Skip          = ofⁿ (Skip≠Assign ∘ _⁻¹)
reflects-instr (Assign x e)   (Assign y g)   =
  dmapʳ (λ x → ap² Assign (x .fst) (x .snd)) (_∘ Assign-inj)
        (reflects-× (discrete-reflects! {x = x} {y = y}) (reflects-aexpr e g))
reflects-instr (Assign _ _)   (Seq _ _)      = ofⁿ Assign≠Seq
reflects-instr (Assign _ _)   (ITE _ _ _)    = ofⁿ Assign≠ITE
reflects-instr (Assign _ _)   (While _ _)    = ofⁿ Assign≠While
reflects-instr (Seq _ _)       Skip          = ofⁿ (Skip≠Seq ∘ _⁻¹)
reflects-instr (Seq _ _)      (Assign _ _)   = ofⁿ (Assign≠Seq ∘ _⁻¹)
reflects-instr (Seq c₁ c₂)    (Seq c₃ c₄)    =
  dmapʳ (λ x → ap² Seq (x .fst) (x .snd)) (_∘ Seq-inj)
        (reflects-× (reflects-instr c₁ c₃) (reflects-instr c₂ c₄))
reflects-instr (Seq _ _)      (ITE _ _ _)    = ofⁿ Seq≠ITE
reflects-instr (Seq _ _)      (While _ _)    = ofⁿ Seq≠While
reflects-instr (ITE _ _ _)     Skip          = ofⁿ (Skip≠ITE ∘ _⁻¹)
reflects-instr (ITE _ _ _)    (Assign _ _)   = ofⁿ (Assign≠ITE ∘ _⁻¹)
reflects-instr (ITE _ _ _)    (Seq _ _)      = ofⁿ (Seq≠ITE ∘ _⁻¹)
reflects-instr (ITE b₁ c₁ c₂) (ITE b₂ c₃ c₄) =
  dmapʳ (λ x → ap (λ q → ITE q c₁ c₂) (x .fst) ∙ ap² (ITE b₂) (x .snd .fst) (x .snd .snd)) (_∘ ITE-inj)
        (reflects-×³ (reflects-bexpr b₁ b₂) (reflects-instr c₁ c₃) (reflects-instr c₂ c₄))
reflects-instr (ITE _ _ _)    (While _ _)    = ofⁿ ITE≠While
reflects-instr (While _ _)     Skip          = ofⁿ (Skip≠While ∘ _⁻¹)
reflects-instr (While _ _)    (Assign _ _)   = ofⁿ (Assign≠While ∘ _⁻¹)
reflects-instr (While _ _)    (Seq _ _)      = ofⁿ (Seq≠While ∘ _⁻¹)
reflects-instr (While _ _)    (ITE _ _ _)    = ofⁿ (ITE≠While ∘ _⁻¹)
reflects-instr (While b₁ c₁)  (While b₂ c₂)  =
  dmapʳ (λ x → ap² While (x .fst) (x .snd)) (_∘ While-inj)
        (reflects-× (reflects-bexpr b₁ b₂) (reflects-instr c₁ c₂))

sym-instr : ∀ {c₁ c₂} → c₁ ==ⁱ c₂ ＝ c₂ ==ⁱ c₁
sym-instr {c₁} {c₂} = reflects-bool-inj (reflects-instr c₁ c₂)
                                        (dmapʳ _⁻¹ (_∘ _⁻¹) (reflects-instr c₂ c₁))

instance
  instr-is-discrete : is-discrete Instr
  instr-is-discrete {x} {y} = (x ==ⁱ y) because reflects-instr x y

instr-is-set : is-set Instr
instr-is-set = is-discrete→is-set instr-is-discrete

asize : Instr → ℕ
asize  Skip         = 1
asize (Assign _ _)  = 1
asize (Seq c₁ c₂)   = asize c₁ + asize c₂
asize (ITE _ c₁ c₂) = 3 + asize c₁ + asize c₂
asize (While _ c)   = 3 + asize c

asize-pos : ∀ i → 0 < asize i
asize-pos  Skip         = z<s
asize-pos (Assign x e)  = z<s
asize-pos (Seq i₁ i₂)   = <-+-r (asize-pos i₁)
asize-pos (ITE b i₁ i₂) = z<s
asize-pos (While b i)   = z<s
