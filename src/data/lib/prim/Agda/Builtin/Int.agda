{-# OPTIONS --without-K #-}

module Agda.Builtin.Int where

open import Agda.Builtin.Nat
open import Agda.Builtin.String

infix 8 pos  -- Standard library uses this as +_

data Int : Set where
  pos    : (n : Nat) → Int
  negsuc : (n : Nat) → Int

{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

primitive primShowInteger : Int → String

{-# COMPILED_JS Int function(x,v) { if (x < 0) { return v.negsuc(-(x+1)); } else { return v.pos(x); }} #-}
{-# COMPILED_JS pos function(x) { return x; } #-}
{-# COMPILED_JS negsuc function(x) { return (-x-1); } #-}
{-# COMPILED_JS primShowInteger function(x) { return x.toString(); } #-}
