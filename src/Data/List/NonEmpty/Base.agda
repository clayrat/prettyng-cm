{-# OPTIONS --safe #-}
module Data.List.NonEmpty.Base where

open import Foundations.Base
open import Meta.Effect.Map

open import Data.Reflects
open import Data.Nat
open import Data.List as List
open import Data.Maybe as Maybe

private
  variable
    ℓ ℓ′ : Level
    A B C : 𝒰 ℓ

infixr 5 _∷¹_

record List⁺ (A : 𝒰 ℓ) : 𝒰 ℓ where
  constructor _∷¹_
  field
    hd : A
    tl : List A

open List⁺ public

uncons : List⁺ A → A × List A
uncons (hd ∷¹ tl) = hd , tl

[_] : A → List⁺ A
[ x ] = x ∷¹ []

infixr 5 _∷⁺_

_∷⁺_ : A → List⁺ A → List⁺ A
x ∷⁺ y ∷¹ xs = x ∷¹ y ∷ xs

len : List⁺ A → ℕ
len (x ∷¹ xs) = suc (List.length xs)

------------------------------------------------------------------------
-- Conversion

to-list : List⁺ A → List A
to-list (x ∷¹ xs) = x ∷ xs

from-list : List A → Maybe (List⁺ A)
from-list []       = nothing
from-list (x ∷ xs) = just (x ∷¹ xs)

from-list-nothing : {xs : List A}
                  → from-list xs ＝ nothing → xs ＝ []
from-list-nothing {xs = []}     p = refl
from-list-nothing {xs = x ∷ xs} p = false! p

from-list-to : {xs : List A} {ns : List⁺ A}
             → ns ∈ₘ from-list xs
             → xs ＝ to-list ns
from-list-to {xs = x ∷ xs} {ns = n ∷¹ ns} p =
  ap to-list (just-inj $ ∈→=just p)

-- Other operations

map⁺ : (A → B) → List⁺ A → List⁺ B
map⁺ f (x ∷¹ xs) = (f x ∷¹ mapₗ f xs)

-- Right fold. Note that s is only applied to the last element (see
-- the examples below).

foldr : (A → B → B) → (A → B) → List⁺ A → B
foldr {A} {B} c s (x ∷¹ xs) = foldr′ x xs
  where
  foldr′ : A → List A → B
  foldr′ x []       = s x
  foldr′ x (y ∷ xs) = c x (foldr′ y xs)

-- Right fold.

foldr₁ : (A → A → A) → List⁺ A → A
foldr₁ f (x ∷¹ xs) = List.rec x f xs

-- Left fold. Note that s is only applied to the first element (see
-- the examples below).

foldl : (B → A → B) → (A → B) → List⁺ A → B
foldl c s (x ∷¹ xs) = List.fold-l c (s x) xs

-- Left fold.

foldl₁ : (A → A → A) → List⁺ A → A
foldl₁ f = foldl f id

-- Append (several variants).

infixr 5 _⁺++⁺_ _++⁺_ _⁺++_

_⁺++⁺_ : List⁺ A → List⁺ A → List⁺ A
(x ∷¹ xs) ⁺++⁺ (y ∷¹ ys) = x ∷¹ (xs List.++ y ∷ ys)

_⁺++_ : List⁺ A → List A → List⁺ A
(x ∷¹ xs) ⁺++ ys = x ∷¹ (xs List.++ ys)

_++⁺_ : List A → List⁺ A → List⁺ A
xs ++⁺ ys = List.rec ys _∷⁺_ xs

concat⁺ : List⁺ (List⁺ A) → List⁺ A
concat⁺ (xs ∷¹ xss) = xs ⁺++ List.concat (mapₗ to-list xss)

concat-map⁺ : (A → List⁺ B) → List⁺ A → List⁺ B
concat-map⁺ f = concat⁺ ∘ map⁺ f

-- Reverse

reverse⁺ : List⁺ A → List⁺ A
reverse⁺ (hd ∷¹ tl) =
  let r = reverse tl in
  Maybe.rec (hd ∷¹ []) (_∷¹ snoc r hd) (r !ᵐ 0)
