module IMP.Syntax (Loc : Set) where

open import Data.Integer as Int using (ℤ)
open import Data.Bool as Bool using (Bool)

infixl 6 _+_ _-_
infixl 7 _*_
data Aexp : Set where
  lit : ℤ → Aexp
  loc : Loc → Aexp
  _+_ _-_ _*_ : Aexp → Aexp → Aexp

infixl 2 _∧_ _∨_
infix 4 _==_ _≤_
infix 2 ¬_
data Bexp : Set where
  lit : Bool → Bexp
  _∧_ _∨_ : Bexp → Bexp → Bexp
  _==_ _≤_ : Aexp → Aexp → Bexp
  ¬_ : Bexp → Bexp

infix 3 _:=_
infixl 2 _>>_
infix 1 if_then_else_
infix 1 while_do_
data Com : Set where
  skip : Com
  _:=_ : Loc → Aexp → Com
  _>>_ : Com → Com → Com
  if_then_else_ : Bexp → Com → Com → Com
  while_do_ : Bexp → Com → Com

data Term : Set where
  aexp : Aexp → Term
  bexp : Bexp → Term
  com  : Com  → Term

Ctx : Set
Ctx = Loc → ℤ
       
data Value : Set where
  aval : ℤ    → Value
  bval : Bool → Value
  ctx  : Ctx  → Value

