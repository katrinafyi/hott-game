# Pi Types

We will try to formulate and prove the statement 

> The sum of two even naturals is even.

## Defining Addition 

To do so we must define `+` on the naturals.
Addition takes in two naturals and spits out a natural, 
so it should have type `ℕ → ℕ → ℕ`.
```agda
_+_ : ℕ → ℕ → ℕ
n + m = ?
```
Try coming up with a sensible definition.
It may not look 'the same' as ours.
<p>
<details>
<summary>Hint</summary>

`n + 0` should be `n` and `n + (m + 1)` should be `(n + m) + 1`
</details>
</p>

## The Statement

Now we can make the statement:
```agda
SumOfEven : (x : Σ ℕ isEven) → (y : Σ ℕ isEven) → isEven (x .fst + y .fst)
SumOfEven x y = ?
```
> Tip: `x .fst` is another notation for `fst x`.
> This works for all sigma types.
There are three ways to interpret this:

- For all even naturals `x` and `y`, 
  their sum is even.
- `isEven (x .fst + y .fst)` is a construction depending on two recipes
  `x` and `y`.
  Given two recipes `x` and `y` of `Σ ℕ isEven`, 
  we break them down into their first components,
  apply the conversion `_+_`,
  and form a recipe for `isEven` of the result.
- `isEven (_ .fst + _ .fst)` is a bundle over the categorical product
  `Σ ℕ isEven × Σ ℕ isEven` and `SumOfEven` is a _section_ of the bundle.
  This means for every point `(x , y)` in `Σ ℕ isEven × Σ ℕ isEven`,
  it gives a point in the fiber `isEven (x .fst + y .fst)`.
  
  (picture)
  
More generally given `A : Type` and `B : A → Type`
we can form the _pi type_ `(x : A) → B x : Type` 
(in other languages `Π (x : ℕ), isEven n`),
with three interpretations : 

- it is the proposition "for all `x : A`, we have `B x`",
  and each term is a collection of proofs `bx : B x`,
  one for each `x : A`.
- recipes of `(x : A) → B x` are made by
  converting each `x : A` to some recipe of `B x`.
  Indeed the function type `A → B` is 
  the special case where 
  the type `B x` is not dependent on `x`. 
  Hence pi types are also known as _dependent function types_.
  Note that terms in the sigma type are pairs `(a , b)` 
  whilst terms in the dependent function type are 
  a collection of pairs `(a , b)` indexed by `a : A`
- Given the bundle `B : A → Type`,
  we have the total space `Σ A B` which is equipped with a projection
  `fst : Σ A B → A`.
  A term of `(x : A) → B x` is a section of this projection.

We are now in a position to prove the statement. Have fun!

## Remarks

_Important_: Once you have proven the statement, 
check out our two ways of defining addition `_+_` and `_+'_`
(in the solutions).

- Use `C-c C-n` to check that they compute the same values
  on different examples.
- Uncomment the code for `Sum'OfEven` in the solutions.
  It is just `SumOfEven` but with `+`s changed for `+'`s.
- Load the file. Does the proof still work?

Our proof `SumOfEven` relied on 
the explicit definition of `_+_`,
which means if we wanted to use our proof on 
someone else's definition of addition, 
it might not work anymore.
> But `_+_` and `_+'_` compute the same values. 
> Are `_+_` and `_+'_` 'the same'? What is 'the same'?

## Another Task : Decidability of `isEven`

As the final task of the Quest,
try to express and prove in agda the statement
> For any natural number it is even or is is not even.
We will make a summary of what is needed:

- a definition of the type `A ⊕ B` (input `\oplus`),
  which has three interpretations
  - the proposition '`A` or `B`'
  - the construction with two ways of making recipes 
    `left : A → A ⊕ B`
    and `right : B → A ⊕ B`.
  - the coproduct of two objects `A` and `B`.
  The type needs to take in parameters `A : Type` and `B : Type`
  ```agda
  data _⊕_ (A : Type) (B : Type) : Type where
    ???
  ```
- a definition of negation. One can motivate it by the following
  - Define `A ↔ B : Type` for two types `A : Type` and `B : Type`.
  - Show that for any `A : Type` we have `(A ↔ ⊥) ↔ (A → ⊥)`
  - Define `¬ : Type → Type` to be `λ A → (A → ⊥)`.
- a formulation and proof of the statement above
