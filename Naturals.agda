module plfa.Naturals where

-- The naturals are an inductive datatype
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
  

-- First task
-- the shorthand for suc (suc (suc (suc (suc (suc (suc zero)))))) is 7


-- A pragma
{-# BUILTIN NATURAL ℕ #-}

-- Imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- Operations on naturals are recursive functions
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
    begin
        2 + 3
    ≡⟨⟩
        suc (1 + 3)
    ≡⟨⟩
        suc (suc (0 + 3))
    ≡⟨⟩
        suc (suc 3)
    ≡⟨⟩
        5
    ∎

-- or we can siply use refl, because agda computes 2+3 and gets 5
-- then 5=5 is reflexive (basicly the same)

_ : 2 + 3 ≡ 5
_ = refl

--Exercise +-example (practice)

_ : 3 + 4 ≡ 7
_ = 
    begin
        3 + 4
    ≡⟨⟩
        suc (2 + 4)
    ≡⟨⟩
        suc (suc (1 + 4))
    ≡⟨⟩
        suc (suc (suc (0 + 4)))
    ≡⟨⟩
        suc (suc (suc 4))
    ≡⟨⟩
        7
    ∎

_ : 3 + 4 ≡ 7
_ = refl

