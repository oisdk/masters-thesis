\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Circle where

open import Prelude
\end{code}
%<*circle-def>
\begin{code}
data S¹ : Type₀ where
  base  : S¹
  loop  : base ≡ base
\end{code}
%</circle-def>
