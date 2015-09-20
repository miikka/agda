
module _ where

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

-- Not allowed:
{-# COMPILED_DATA Bool Bool True False #-}
