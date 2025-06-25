open import Data.Nat.Base

module Text.Pretty (width : ℕ) where

open import Foundations.Prelude
open import Meta.Effect

open import Data.Bool  -- .Base   using (Char)
open import Data.Char  -- .Base   using (Char)
open import Data.List  --.Base   using (List; []; _∷_)
open import Data.Maybe as Maybe  -- .Base    using (ℕ)
open import Data.String -- .Base

open import Data.Nat.Order.Base

open import Data.List.NonEmpty as List⁺

------------------------------------------------------------------------
-- Internal representation of documents and rendering function

import Text.Pretty.Core as Core

record Doc : 𝒰 where
  constructor mkDoc
  field runDoc : List Core.Block
open Doc public


render : Doc → String
render = Core.render
       ∘ Maybe.rec Core.empty (  foldr₁ (λ l r → -- TODO inlined max
                                           if l .Core.Block.height ≤? r .Core.Block.height
                                             then r
                                             else l)
                               ∘ _∷¹_ $²_) 
       ∘ unconsᵐ
       ∘ runDoc

------------------------------------------------------------------------
-- Basic building blocks

failD : Doc
failD = mkDoc []

text : String → Doc
text = mkDoc ∘ filter (Core.valid? width) ∘ (_∷ []) ∘ Core.text

emptyD : Doc
emptyD = text ""

char : Char → Doc
char c = text (list→string (c ∷ []))

spaces : ℕ → Doc
spaces n = text (list→string $ replicate n ' ')

semi colon comma space dot : Doc
semi = char ';'; colon = char ':'
comma = char ','; space = char ' '; dot = char '.'

backslash forwardslash equal : Doc
backslash = char '\\'; forwardslash = char '/'; equal = char '='

squote dquote : Doc
squote = char '\''; dquote = char '"'

lparen rparen langle rangle lbrace rbrace lbracket rbracket : Doc
lparen = char '('; rparen = char ')'
langle = char '<'; rangle = char '>'
lbrace = char '{'; rbrace = char '}'
lbracket = char '['; rbracket = char ']'

------------------------------------------------------------------------
-- Combining two documents

infixr 5 _◆_
_◆_ : Doc → Doc → Doc
x ◆ y = mkDoc $
        filter (Core.valid? width) $
        Core._◆_ <$> runDoc x <*> runDoc y

flush : Doc → Doc
flush d = mkDoc (Core.flush <$> runDoc d)

-- horizontal concatenation
infixr 5 _◈_
_◈_ : Doc → Doc → Doc
x ◈ y = x ◆ space ◆ y

-- vertical concatenation
infixr 5 _$$_
_$$_ : Doc → Doc → Doc
x $$ y = flush x ◆ y

infixr 4 _⟨|⟩_
_⟨|⟩_ : Doc → Doc → Doc
x ⟨|⟩ y = mkDoc (runDoc x ++ runDoc y)

------------------------------------------------------------------------
-- Combining lists of documents

foldDoc : (Doc → Doc → Doc) → List Doc → Doc
foldDoc _ []       = emptyD
foldDoc _ (x ∷ []) = x
foldDoc f (x ∷ xs) = f x (foldDoc f xs)

hsep vcat : List Doc → Doc
hsep = foldDoc _◈_
vcat = foldDoc _$$_

sep : List Doc → Doc
sep [] = emptyD
sep xs@(_ ∷ _) = hsep xs ⟨|⟩ vcat xs

------------------------------------------------------------------------
-- Defined combinators

parens : Doc → Doc
parens d = lparen ◆ d ◆ rparen

commaSep : List Doc → Doc
commaSep = foldDoc λ d e → d ◆ comma ◈ e

newline : Doc
newline = flush emptyD
