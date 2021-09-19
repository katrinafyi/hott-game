module 1FundamentalGroup.Quest0 where

open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming ( Unit to ⊤ )
open import Cubical.Data.Bool
open import Cubical.Foundations.Prelude renaming ( subst to endPt )
open import Cubical.Foundations.Isomorphism renaming ( Iso to _≅_ )
open import Cubical.Foundations.Path
open import Cubical.HITs.S1

Refl : base ≡ base
Refl = {!!}

Flip : Bool → Bool
Flip x = {!!}

flipIso : Bool ≅ Bool
flipIso = {!!}

flipPath : Bool ≡ Bool
flipPath = {!!}

doubleCover : S¹ → Type
doubleCover x = {!!}

endPtOfTrue : (p : base ≡ base) → doubleCover base
endPtOfTrue p = {!!}

Refl≢loop : Refl ≡ loop → ⊥
Refl≢loop p = {!!}
