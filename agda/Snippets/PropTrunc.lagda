\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.PropTrunc where

open import Level
open import Path
\end{code}
%<*prop-trunc-def>
\begin{code}[number=prop-trunc]
data ∥_∥ (A : Type a) : Type a where
  ∣_∣      : A → ∥ A ∥
  squash   :  (x y : ∥ A ∥) → x ≡ y
\end{code}
%</prop-trunc-def>
