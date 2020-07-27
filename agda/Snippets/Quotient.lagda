\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Quotient where

open import Prelude
-- open import Cubical.HITs.SetQuotients

\end{code}
%<*quot-def>
\begin{code}
data _/_ (A : Type a) (R : A → A → Type b) : Type (a ℓ⊔ b) where
  [_] : (x : A) → A / R
  eq/ : (x y : A) → (r : R x y) → [ x ] ≡ [ y ]
  squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q
\end{code}
%</quot-def>
