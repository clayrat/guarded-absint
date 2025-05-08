module SPA.Sign where

open import Prelude
open import Data.Empty hiding (_≠_)
open import Data.Unit
open import Data.Dec

data Sign : 𝒰 where
  pl : Sign
  mi : Sign
  ze : Sign

is-pl : Sign → 𝒰
is-pl pl = ⊤
is-pl mi = ⊥
is-pl ze = ⊥

is-mi : Sign → 𝒰
is-mi pl = ⊥
is-mi mi = ⊤
is-mi ze = ⊥

pl≠mi : pl ≠ mi
pl≠mi e = subst is-pl e tt

pl≠ze : pl ≠ ze
pl≠ze e = subst is-pl e tt

mi≠ze : mi ≠ ze
mi≠ze e = subst is-mi e tt

Sign-discrete : is-discrete Sign
Sign-discrete {x = pl} {y = pl} = yes refl
Sign-discrete {x = pl} {y = mi} = no pl≠mi
Sign-discrete {x = pl} {y = ze} = no pl≠ze
Sign-discrete {x = mi} {y = pl} = no (pl≠mi ∘ _⁻¹)
Sign-discrete {x = mi} {y = mi} = yes refl
Sign-discrete {x = mi} {y = ze} = no mi≠ze
Sign-discrete {x = ze} {y = pl} = no (pl≠ze ∘ _⁻¹)
Sign-discrete {x = ze} {y = mi} = no (mi≠ze ∘ _⁻¹)
Sign-discrete {x = ze} {y = ze} = yes refl
