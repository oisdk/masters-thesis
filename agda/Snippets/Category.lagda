\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Category where

open import Level
open import Data.Sigma
open import HLevels hiding (hSet)

Ob : Type₁
\end{code}
%<*hset>
\begin{code}
Ob = Σ[ t ⦂ Type₀ ] isSet t
\end{code}
%</hset>
