{-# OPTIONS --without-K #-}

module Agda.Builtin.Nat where

open import Agda.Builtin.Bool

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}
{-# COMPILED_JS Nat function(x,v) { if (x < 1) { return v.zero(); } else { return v.suc(x-1); } } #-}
{-# COMPILED_JS zero 0 #-}
{-# COMPILED_JS suc function(x) { return x+1; } #-}

infix  4 _==_ _<_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATPLUS _+_ #-}
{-# COMPILED_JS _+_ function (x) { return function (y) { return x+y; }; } #-}

_-_ : Nat → Nat → Nat
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

{-# BUILTIN NATMINUS _-_ #-}
{-# COMPILED_JS _-_ function(x) { return function (y) {
                                      return Math.max(x-y, 0); }; } #-}

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + n * m

{-# BUILTIN NATTIMES _*_ #-}
{-# COMPILED_JS _*_ function (x) { return function (y) { return x*y; }; } #-}

_==_ : Nat → Nat → Bool
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false

{-# BUILTIN NATEQUALS _==_ #-}
{-# COMPILED_JS _==_ function(x) { return function(y) { return x === y; }; } #-}

_<_ : Nat → Nat → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m

{-# BUILTIN NATLESS _<_ #-}
{-# COMPILED_JS _<_ function(x) { return function(y) { return x<y; }; } #-}

div-helper : Nat → Nat → Nat → Nat → Nat
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j

{-# BUILTIN NATDIVSUCAUX div-helper #-}

mod-helper : Nat → Nat → Nat → Nat → Nat
mod-helper k m  zero    j      = k
mod-helper k m (suc n)  zero   = mod-helper 0 m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

{-# BUILTIN NATMODSUCAUX mod-helper #-}
