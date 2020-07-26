\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Equality where

open import Level

private
  module MLTTEquality where
\end{code}
%<*equality-def>
\begin{code}
    data _≡_ {a} {A : Type a} (x : A) : A → Type a where
      refl : x ≡ x
\end{code}
%</equality-def>
