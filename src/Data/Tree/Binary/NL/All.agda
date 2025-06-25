{-# OPTIONS --safe #-}
module Data.Tree.Binary.NL.All where

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
    ℓⁿ ℓˡ ℓp ℓq ℓr ℓs ℓ ℓ′ : Level
    N : 𝒰 ℓⁿ
    L : 𝒰 ℓˡ
    A : 𝒰 ℓ
    B : 𝒰 ℓ′
    P : Pred N ℓp
    Q : Pred L ℓq
    R : Pred N ℓr
    S : Pred L ℓs

-- TODO variadics fail
all-map : (∀ {n} → P n → R n) → (∀ {l} → Q l → S l) → ∀[ All P Q ⇒ All R S ]
all-map f g (leaf x)     = leaf (g x)
all-map f g (node l m r) = node (all-map f g l) (f m) (all-map f g r)

all-mapₙ : (∀ {n} → P n → R n) → ∀[ All P Q ⇒ All R Q ]
all-mapₙ {Q = Q} f = all-map f id

all-mapₗ : (∀ {l} → Q l → S l) → ∀[ All P Q ⇒ All P S ]
all-mapₗ {P = P} f = all-map id f

map⁺ : (f : N → A) → (g : L → B)
     → ∀ {t} → All (P ∘ f) (Q ∘ g) t → All P Q (map f g t)
map⁺ f g (leaf x)     = leaf x
map⁺ f g (node l m r) = node (map⁺ f g l) m (map⁺ f g r)

mapₙ⁺ : ∀ (f : N → A) {t}
      → All (P ∘ f) Q t → All P Q (mapₙ f t)
mapₙ⁺ f = map⁺ f id

mapₗ⁺ : ∀ (g : L → B) {t}
      → All P (Q ∘ g) t → All P Q (mapₗ g t)
mapₗ⁺ g = map⁺ id g

