module Trinitarianism.Quest1Solutions where

open import Trinitarianism.Preambles.P1

isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n


existsEven : Σ ℕ isEven
existsEven = 4 , tt

div2 : Σ ℕ isEven → ℕ
div2 (0 , tt) = 0
div2 (suc (suc n) , hn) = suc (div2 (n , hn))