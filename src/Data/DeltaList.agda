{-# OPTIONS --safe #-}
module Data.DeltaList where

open import Foundations.Base

open import Data.List.Base
open import Data.Nat.Base

private
  variable
    ℓ ℓ′ : Level
    A : 𝒰 ℓ
    B : 𝒰 ℓ′

DeltaList : 𝒰 ℓ → 𝒰 ℓ
DeltaList A = List A → List A

liftL : (List A → List A) → (DeltaList A → DeltaList A)
liftL f xs k = f (xs k)

[]d : DeltaList A
[]d k = k

_∷d_ : A → DeltaList A → DeltaList A
_∷d_ x = liftL (x ∷_)

[_]d : A → DeltaList A
[ x ]d = x ∷d []d

_++d_ : DeltaList A → DeltaList A → DeltaList A
(xs ++d ys) k = xs (ys k)

infixl 6 _∷ʳ_
_∷ʳ_ : DeltaList A → A → DeltaList A
(xs ∷ʳ x) k = xs (x ∷ k)

to-list : DeltaList A → List A
to-list xs = xs []

-- linear in the length of xs.

from-list : List A → DeltaList A
from-list xs = xs ++_
