-- ignore
module 1FundamentalGroup.Quest0 where
open import 1FundamentalGroup.Preambles.P0

Refl : base ≡ base
Refl = λ i → base

Flip : Bool → Bool
Flip false = true
Flip true = false

flipIso : Bool ≅ Bool
flipIso = iso Flip Flip rightInv leftInv where

  rightInv : section Flip Flip
  rightInv false = refl
  rightInv true = refl

  leftInv : retract Flip Flip
  leftInv x = rightInv x

flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

doubleCover : S¹ → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

endPtOfTrue : base ≡ base → doubleCover base
endPtOfTrue p = endPt doubleCover p true

Refl≢loop : Refl ≡ loop → ⊥
Refl≢loop p = true≢false (cong endPtOfTrue p)

------------------- Side Quest - Empty -------------------------

-- This is a comment box,
-- remove the {- and -} to do the side quests

toEmpty : (A : Type) → Type
toEmpty A = A → ⊥

pathEmpty : (A : Type) → Type₁
pathEmpty A = A ≡ ⊥

isoEmpty : (A : Type) → Type
isoEmpty A = A ≅ ⊥

outOf⊥ : (A : Type) → ⊥ → A
outOf⊥ A ()

toEmpty→isoEmpty : (A : Type) → toEmpty A → isoEmpty A
toEmpty→isoEmpty A x = iso x (outOf⊥ A) l r
  where
    l : section x (outOf⊥ A)
    l ()

    r : retract x (outOf⊥ A)
    r y = outOf⊥ (outOf⊥ A (x y) ≡ y) (x y)

isoEmpty→pathEmpty : (A : Type) → isoEmpty A → pathEmpty A
isoEmpty→pathEmpty A x = isoToPath x

pathEmpty→toEmpty : (A : Type) → pathEmpty A → toEmpty A
pathEmpty→toEmpty A p = λ x → pathToFun p x

------------------- Side Quests - true≢false --------------------

-- This is a comment box,
-- remove the {- and -} to do the side quests

true≢false' : true ≡ false → ⊥
true≢false' p = pathToFun (cong f p) tt
  where
    f : Bool → Type
    f false = ⊥
    f true = ⊤



