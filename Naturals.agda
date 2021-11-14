module plfa.Naturals where

-- The naturals are an inductive datatype

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
  

-- the shorthand for suc (suc (suc (suc (suc (suc (suc zero)))))) is 7

-- A pragma
{-# BUILTIN NATURAL ℕ #-}

-- Imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

