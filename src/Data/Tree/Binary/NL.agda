{-# OPTIONS --safe #-}
module Data.Tree.Binary.NL where

open import Foundations.Base

open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat.Base
open import Data.List.Base
open import Data.DeltaList

data Tree {ℓⁿ ℓˡ} (N : 𝒰 ℓⁿ) (L : 𝒰 ℓˡ) : 𝒰 (ℓⁿ ⊔ ℓˡ) where
  leaf  : L → Tree N L
  node  : Tree N L → N → Tree N L → Tree N L

private
  variable
    ℓⁿ ℓˡ ℓ ℓ′ : Level
    N : 𝒰 ℓⁿ
    L : 𝒰 ℓˡ
    A : 𝒰 ℓ
    B : 𝒰 ℓ′

map : (N → A) → (L → B) → Tree N L → Tree A B
map f g (leaf x)     = leaf (g x)
map f g (node l m r) = node (map f g l) (f m) (map f g r)

mapₙ : (N → A) → Tree N L → Tree A L
mapₙ f t = map f id t

mapₗ : (L → B) → Tree N L → Tree N B
mapₗ f t = map id f t

#nodes : Tree N L → ℕ
#nodes (leaf _)     = 0
#nodes (node l _ r) = #nodes l + suc (#nodes r)

fold-r : (A → N → A → A) → (L → A) → Tree N L → A
fold-r f g (leaf x)     = g x
fold-r f g (node l m r) = f (fold-r f g l) m (fold-r f g r)

to-prefix-delta : Tree N L → DeltaList N
to-prefix-delta = fold-r (λ l m r → m ∷d (l ++d r)) (λ _ → []d)

to-prefix : Tree N L → List N
to-prefix = to-list ∘ to-prefix-delta

to-infix-delta : Tree N L → DeltaList N
to-infix-delta = fold-r (λ l m r → l ++d (m ∷d r)) (λ _ → []d)

to-infix : Tree N L → List N
to-infix = to-list ∘ to-infix-delta
