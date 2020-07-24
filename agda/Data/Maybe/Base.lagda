\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Base where

open import Level
\end{code}
%<*maybe-def>
\begin{code}
data Maybe (A : Type a) : Type a where
  nothing  : Maybe A
  just     : A → Maybe A
\end{code}
%</maybe-def>
\begin{code}

maybe : {B : Maybe A → Type b} → B nothing → ((x : A) → B (just x)) → (x : Maybe A) → B x
maybe b f nothing = b
maybe b f (just x) = f x
\end{code}
