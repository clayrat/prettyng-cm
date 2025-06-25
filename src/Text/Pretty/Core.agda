------------------------------------------------------------------------
-- This module is based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
------------------------------------------------------------------------

module Text.Pretty.Core where

open import Foundations.Prelude

open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.List.Operations.Properties
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.All as Allᴹ
open import Data.String
open import Data.String.Properties.Unsafe

open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open import Order.Diagram.Join
import Order.Diagram.Join.Reasoning as JR
open decminmax ℕ-dec-total
open JR ℕₚ max-joins

open import Data.Refinement
open import Data.Tree.Binary.NL
open import Data.Tree.Binary.NL.All as Allᵀ
open import Data.Tree.Binary.NL.Properties

{-
import Level

open import Data.Bool.Base using (Bool)
open import Data.Irrelevant as Irrelevant using (Irrelevant) hiding (module Irrelevant)
open import Data.List.Base as List   using (List; []; _∷_)
open import Data.Nat.Base            using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties      using (≤-refl; ≤-trans; +-identityʳ;
  module ≤-Reasoning; m≤n⊔m; +-monoʳ-≤; m≤m⊔n; +-comm; _≤?_)
open import Data.Product.Base as Prod using (_×_; _,_; uncurry; proj₁; proj₂)
import Data.Product.Relation.Unary.All as Allᴾ

open import Data.Tree.Binary as Tree using (Tree; leaf; node; #nodes; mapₙ)
open import Data.Tree.Binary.Relation.Unary.All as Allᵀ using (leaf; node)
open import Data.Unit.Base using (⊤; tt)
import Data.Tree.Binary.Relation.Unary.All.Properties as Allᵀ
import Data.Tree.Binary.Properties as Tree

open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Maybe.Relation.Unary.All as Allᴹ using (nothing; just)

open import Data.String.Base as String
  using (String; length; replicate; _++_; unlines)
import Data.String.Unsafe as String
open import Function.Base using (_∘_; flip; _on_; id; _∘′_; _$_)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Unary using (IUniversal; _⇒_; U)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

open import Data.Refinement using (Refinement-syntax; _,_; value; proof)
import Data.Refinement.Relation.Unary.All as Allᴿ
-}

------------------------------------------------------------------------
-- Block of text

-- Content is a representation of the first line and the middle of the
-- block. We use a tree rather than a list for the middle of the block
-- so that we can extend it with lines on the left and on the line for
-- free. We will ultimately render the block by traversing the tree left
-- to right in a depth-first manner.

TreeStr : 𝒰
TreeStr = Tree String ⊤

Content : 𝒰
Content = Maybe (String × TreeStr)

sizeC : Content → ℕ
sizeC = Maybe.rec 0 (suc ∘ #nodes ∘ snd)

AllC : ∀ {ℓ} (P : String → 𝒰 ℓ) → (Content → 𝒰 ℓ)
AllC P c = Allᴹ.All (λ st → P (st .fst) × Allᵀ.All P (λ _ → ⊤) (st .snd)) c

All≤ : ℕ → Content → 𝒰
All≤ n = AllC (λ s → lengthₛ s ≤ n)

record Block : 𝒰 where
  field
    height    : ℕ
    block     : [ xs ꞉ Content ∣ sizeC xs ＝ height ]₀
  -- last line
    lastWidth : ℕ
    lastL     : [ s ꞉ String ∣ lengthₛ s ＝ lastWidth ]₀
  -- max of all the widths
    maxWidth  : [ n ꞉ ℕ ∣ (lastWidth ≤ n) × All≤ n (block .value) ]₀

------------------------------------------------------------------------
-- Raw string

text : String → Block
text s = record
  { height    = 0
  ; block     = nothing ,₀ refl
  ; lastWidth = width
  ; lastL     = s ,₀ refl
  ; maxWidth  = width ,₀ (refl , nothing)
  } where width = lengthₛ s

------------------------------------------------------------------------
-- Empty

empty : Block
empty = text ""

------------------------------------------------------------------------
-- Helper functions

node? : Content → String → TreeStr → Content
node? (just (x , xs)) y ys = just (x , node xs y ys)
node? nothing         y ys = just (y , ys)

∣node?∣ : ∀ b y ys
        → sizeC (node? b y ys) ＝ sizeC b + suc (#nodes ys)
∣node?∣ (just (x , xs)) y ys = refl
∣node?∣ nothing         y ys = refl

≤-Content : ∀ {m n} {b : Content} → m ≤ n → All≤ m b → All≤ n b
≤-Content {m} {n} m≤n =
  Allᴹ.all-map λ where
                  (le , a) → (le ∙ m≤n) , all-mapₙ (_∙ m≤n) a

All≤-node? : ∀ {l m r n}
           → All≤ n l → lengthₛ m ≤ n
           → Allᵀ.All (λ s → lengthₛ s ≤ n) (λ _ → ⊤) r
           → All≤ n (node? l m r)
All≤-node?  nothing          py pys = just (py , pys)
All≤-node? (just (px , pxs)) py pys = just (px , node pxs py pys)

------------------------------------------------------------------------
-- Appending two documents

private
  module append (x y : Block) where

    module x = Block x
    module y = Block y

    blockx = x.block .value
    blocky = y.block .value

    widthx = x.maxWidth .value
    widthy = y.maxWidth .value

    lastx = x.lastL .value
    lasty = y.lastL .value

    height : ℕ
    height = x.height + y.height

    lastWidth : ℕ
    lastWidth = x.lastWidth + y.lastWidth

    pad : Maybe String
    pad =
      let l = x.lastWidth in
      if is-zero? l
        then nothing
        else just (list→string (replicate l ' '))

    size-pad : Maybe.rec 0 lengthₛ pad ＝ x.lastWidth
    size-pad with x.lastWidth
    ... | zero  = refl
    ... | suc n =   ap length (list→string→list {xs = _ ∷ _})
                  ∙ ap suc length-replicate

    indent : Maybe String → String → String
    indent = Maybe.rec id _++ₛ_

    size-indent : ∀ ma str
                → lengthₛ (indent ma str) ＝ Maybe.rec 0 lengthₛ ma + lengthₛ str
    size-indent (just pad) str = lengthₛ-++ₛ {s₁ = pad}
    size-indent  nothing   str = refl

    indents : Maybe String → TreeStr → TreeStr
    indents = Maybe.rec id (mapₙ ∘ _++ₛ_)

    size-indents : ∀ ma t → #nodes (indents ma t) ＝ #nodes t
    size-indents (just pad) t = #nodes-mapₙ (pad ++ₛ_) t
    size-indents  nothing   t = refl
    
    unfold-indents : ∀ ma t → indents ma t ＝ mapₙ (indent ma) t
    unfold-indents (just x) t = refl
    unfold-indents  nothing t = map-id t ⁻¹

    vContent : Content × String
    vContent =
      Maybe.rec
        (blockx , lastx ++ₛ lasty)
        (λ where (hd , tl) → node?
                    {-,--------------,-}
                    {-|-} blockx   {-|-}
                    {-|-}          {-'---,-}     {-,------------------,-}
                    {-|-} (lastx       {-|-} ++ₛ {-|-}  hd)         {-|-}
                    {-'------------------'-}     {-|-}              {-|-}
                    (indents pad                 {-|-}  tl)    {-,----'-}
                    , indent pad                 {-|-} lasty   {-|-}
                                                 {-'-------------'-})
        blocky

    vBlock = fst vContent
    vLast  = snd vContent

    isBlock : sizeC blockx ＝ x.height
            → sizeC blocky ＝ y.height
            → sizeC vBlock ＝ height
    isBlock sx sy with blocky
    ... | just (hd , tl) =
              ∣node?∣ blockx _ _
             ∙ ap² _+_ sx (ap suc (size-indents pad _) ∙ sy)
    ... | nothing = sx ∙ +-zero-r _ ⁻¹
                       ∙ ap (x.height +_) sy

    block : [ xs ꞉ Content ∣ sizeC xs ＝ height ]₀
    block .value = vBlock
    block .proof = isBlock (x.block .proof) (y.block .proof)

    isLastLine : lengthₛ lastx ＝ x.lastWidth
               → lengthₛ lasty ＝ y.lastWidth
               → lengthₛ vLast ＝ lastWidth
    isLastLine sx sy with blocky
    ... | just (hd , tl) =   size-indent pad lasty
                           ∙ ap² _+_ size-pad sy
    ... | nothing        =   lengthₛ-++ₛ {s₁ = lastx}
                           ∙ ap² _+_ sx sy

    lastL : [ s ꞉ String ∣ lengthₛ s ＝ lastWidth ]₀
    lastL .value = vLast
    lastL .proof = isLastLine (x.lastL .proof) (y.lastL .proof)

    vMaxWidth : ℕ
    vMaxWidth = max widthx (x.lastWidth + widthy)

    isMaxWidth₁ : y.lastWidth ≤ widthy → lastWidth ≤ vMaxWidth
    isMaxWidth₁ p = ≤-+ refl p ∙ r≤∪ {x = widthx}

    isMaxWidth₂ : lengthₛ lastx ＝ x.lastWidth
                → x.lastWidth ≤ widthx
                → All≤ widthx blockx
                → All≤ widthy blocky
                → All≤ vMaxWidth vBlock
    isMaxWidth₂ xe xle sx sy with blocky
    isMaxWidth₂ xe xle sx sy | nothing        = ≤-Content l≤∪ sx
    isMaxWidth₂ xe xle sx (just (shd , stl)) | just (hd , tl) =
      All≤-node? (≤-Content l≤∪ sx)
                 middle
                 (subst (Allᵀ.All _ (λ _ → ⊤)) (unfold-indents pad tl ⁻¹) $
                  mapₙ⁺ (indent pad) $
                  all-mapₙ (λ {n} → indented n) stl)
      where
      middle : lengthₛ (lastx ++ₛ hd) ≤ vMaxWidth
      middle =   =→≤ (lengthₛ-++ₛ {s₁ = lastx} {s₂ = hd})
               ∙ ≤-+ (=→≤ xe) shd 
               ∙ r≤∪ {x = widthx}

      indented : ∀ s
               → lengthₛ s ≤ widthy
               → lengthₛ (indent pad s) ≤ vMaxWidth
      indented s ss =   =→≤ (size-indent pad s)
                      ∙ ≤-+ (=→≤ size-pad) ss 
                      ∙ r≤∪ {x = widthx}

    maxWidth : [ n ꞉ ℕ ∣ (lastWidth ≤ n) × All≤ n vBlock ]₀
    maxWidth .value = vMaxWidth
    maxWidth .proof =   isMaxWidth₁ (y.maxWidth .proof .fst)
                      , isMaxWidth₂ (x.lastL .proof)
                                    (x.maxWidth .proof .fst)
                                    (x.maxWidth .proof .snd)
                                    (y.maxWidth .proof .snd)
 
infixl 4 _◆_
_◆_ : Block → Block → Block
x ◆ y = record { append x y }

------------------------------------------------------------------------
-- Flush (introduces a new line)

private
  module flush (x : Block) where

    module x = Block x
    blockx  = x.block .value
    lastx   = x.lastL .value
    widthx  = x.maxWidth .value
    heightx = x.height

    height    = suc heightx
    lastWidth = 0
    vMaxWidth = widthx

    lastL : [ s ꞉ String ∣ lengthₛ s ＝ lastWidth ]₀
    lastL = "" ,₀ refl

    vContent = node? blockx lastx (leaf tt)

    isBlock : sizeC blockx ＝ heightx → sizeC vContent ＝ height
    isBlock sx = ∣node?∣ blockx lastx (leaf tt) ∙ +-comm (sizeC blockx) 1 ∙ ap suc sx 

    block : [ xs ꞉ Content ∣ sizeC xs ＝ height ]₀
    block .value = vContent
    block .proof = isBlock (x.block .proof)

    maxWidth : [ n ꞉ ℕ ∣ (lastWidth ≤ n) × All≤ n vContent ]₀
    maxWidth .value = widthx
    maxWidth .proof =
      z≤ , All≤-node? (x.maxWidth .proof .snd)
                      (=→≤ (x.lastL .proof) ∙ x.maxWidth .proof .fst)
                      (leaf tt)

flush : Block → Block
flush x = record { flush x }

------------------------------------------------------------------------
-- Other functions

render : Block → String
render x = lines
  $ Maybe.rec [] ((λ hd tl → hd ∷ to-infix tl) $²_) 
  $ node? (x .Block.block .value) (x .Block.lastL .value) (leaf tt)

valid? : ℕ → Block → Bool
valid? width b = Block.maxWidth b .value ≤? width
