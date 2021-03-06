module Prelude.Nat where

open import Prelude.Bool

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

infixl 30 _+_

_+_ : Nat -> Nat -> Nat
Z   + m = m
S n + m = S (n + m)

{-# BUILTIN NATPLUS _+_ #-}

_*_ : Nat -> Nat -> Nat
Z   * m = Z
S n * m = (n * m) + m

{-# BUILTIN NATTIMES _*_ #-}

_-_ : Nat -> Nat -> Nat
n     - Z     = n
(S n) - (S m) = n - m
Z     - _     = Z

{-# BUILTIN NATMINUS _-_ #-}

_<_ : Nat -> Nat -> Bool
_   < Z   = false
Z   < S _ = true
S n < S m = n < m

-- {-# BUILTIN NATLESS _<_ #-}

Nid : Nat -> Bool -> Bool
Nid Z     true  = true
Nid Z     false = false
Nid (S n) m     =  (Nid n ( m))

-- {-# BUILTIN NATEQUALS __ #-}
