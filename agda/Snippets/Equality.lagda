\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Equality where

open import Level

module MLTTEquality where
\end{code}
%<*equality-def>
\begin{code}
  data _≡_ {a} {A : Type a} (x : A) : A → Type a where
    refl : x ≡ x
\end{code}
%</equality-def>
\begin{code}
open import Prelude hiding (sym; refl)

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
%<*refl-def>
\begin{code}
refl : x ≡ x
refl {x = x} i = x
\end{code}
%</refl-def>
\begin{code}
-- J : ∀ {a} {A : Type a} (P : (x y : A) → x ≡ y → Type b) →
--     ((x : A) → P x x refl) → (x y : A) (x≡y : x ≡ y) → P x y x≡y
-- J = {!!}
\end{code}
