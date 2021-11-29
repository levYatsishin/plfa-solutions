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

-- Multiplication
_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- *-example (practice)
_ : 3 * 4 ≡ 12
_ = 
    begin
        3 * 4
    ≡⟨⟩
        4 + (2 * 4)
    ≡⟨⟩
        4 + (4 + (1 * 4))
    ≡⟨⟩
        4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩
        4 + (4 + (4 + 0))
    ≡⟨⟩
        8 + 4
    ≡⟨⟩
        12
    ∎

--or with refl
_ : 3 * 4 ≡ 12
_ = refl

-- Exercise _^_ (recommended)
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = refl

-- Monus
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ : 5 ∸ 3 ≡ 2
_ = 
    begin
        5 ∸ 3
    ≡⟨⟩
        4 ∸ 2
    ≡⟨⟩
        3 ∸ 1
    ≡⟨⟩
        2 ∸ 0
    ≡⟨⟩
        2
    ∎

_ : 3 ∸ 5 ≡ 0
_ = 
    begin
        3 ∸ 5
    ≡⟨⟩
        2 ∸ 4
    ≡⟨⟩
        1 ∸ 3
    ≡⟨⟩
        0 ∸ 2
    ≡⟨⟩
        0
    ∎

-- Precedence
infixl 6  _+_  _∸_
infixl 7  _*_

-- More pragmas
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise Bin (stretch)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- inc func
inc : Bin → Bin
inc(⟨⟩) = ⟨⟩ I
inc(b O) = b I
inc(b I) = inc b O

_ : inc(⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc(⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ O O O O) ≡ ⟨⟩ O O O I
_ = refl


-- from func
from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1


_ : from (⟨⟩) ≡ 0
_ = refl

_ : from (⟨⟩ O O O O I) ≡ 1
_ = refl

_ : from (⟨⟩ O O O O I) ≡ from (⟨⟩ O I)
_ = refl



-- to func
to   : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

_ : to (0) ≡ ⟨⟩
_ = refl

_ : to (1) ≡ ⟨⟩ I
_ = refl

-- Standard library
-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
