{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Sugar where

open import Prelude
open import Data.Maybe

_>>=_ : Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x >>= f = f x

pure : A → Maybe A
pure = just

_<*>_ : Maybe (A → B) → Maybe A → Maybe B
nothing <*> xs = nothing
just f <*> nothing = nothing
just f <*> just x = just (f x)
