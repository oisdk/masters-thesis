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
\begin{code}
open import Prelude hiding (sym)

private
  variable
    x y : A
\end{code}
%<*sym-def>
\begin{code}
sym : x ≡ y → y ≡ x
sym x≡y i = x≡y (~ i)
\end{code}
%</sym-def>
