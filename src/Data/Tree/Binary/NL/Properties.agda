{-# OPTIONS --safe #-}
module Data.Tree.Binary.NL.Properties where

open import Meta.Prelude
open Variadics _

open import Data.Tree.Binary.NL

data All {ℓⁿ ℓˡ ℓᵖ ℓ𐞥} {N : 𝒰 ℓⁿ} {L : 𝒰 ℓˡ}
         (P : Pred N ℓᵖ) (Q : Pred L ℓ𐞥)
       : Tree N L → 𝒰 (ℓⁿ ⊔ ℓˡ ⊔ ℓᵖ ⊔ ℓ𐞥) where
  leaf : ∀ {x} → Q x → All P Q (leaf x)
  node : ∀ {l m r} → All P Q l → P m → All P Q r → All P Q (node l m r)

private
  variable
    ℓⁿ ℓˡ ℓ ℓ′ : Level
    N : 𝒰 ℓⁿ
    L : 𝒰 ℓˡ
    A : 𝒰 ℓ
    B : 𝒰 ℓ′
    
#nodes-map : ∀ (f : N → A) (g : L → B) t → #nodes (map f g t) ＝ #nodes t
#nodes-map f g (leaf x)     = refl
#nodes-map f g (node l m r) =
  ap² (λ l r → l + suc r) (#nodes-map f g l) (#nodes-map f g r)

#nodes-mapₙ : (f : N → A) (t : Tree N L) → #nodes (mapₙ f t) ＝ #nodes t
#nodes-mapₙ f = #nodes-map f id

#nodes-mapₗ : (g : L → B) (t : Tree N L) → #nodes (mapₗ g t) ＝ #nodes t
#nodes-mapₗ = #nodes-map id

map-id : (t : Tree N L) → map id id t ＝ t
map-id (leaf x)     = refl
map-id (node l v r) = ap² (λ x y → node x v y) (map-id l) (map-id r)
