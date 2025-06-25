{-# OPTIONS --safe #-}
module Data.Refinement where

open import Foundations.Base

{-
private
  variable
    a b p q : Level
    A : Set a
    B : Set b
    P : A → Set p
    Q : A → Set q
-}

record Refine {ℓa ℓp} (A : 𝒰 ℓa) (P : A → 𝒰 ℓp) : 𝒰 (ℓa ⊔ ℓp) where
  constructor _,₀_
  field value : A
        @0 proof : P value
open Refine public

-- The syntax declaration below is attached to Refine-syntax, to make it
-- easy to import Refine without the special syntax.

infix 2 Refine-syntax

Refine-syntax = Refine

syntax Refine-syntax A (λ x → P) = [ x ꞉ A ∣ P ]₀

{-
map : (f : A → B) → (∀ {a} → P a → Q (f a)) → [ a ∈ A ∣ P a ] → [ b ∈ B ∣ Q b ]
map f prf (a , p) = f a , Erased.map prf p

refine : (∀ {a} → P a → Q a) → [ a ∈ A ∣ P a ] → [ a ∈ A ∣ Q a ]
refine = map id
-}
