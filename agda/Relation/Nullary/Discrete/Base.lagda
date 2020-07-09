\begin{code}
{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Discrete.Base where

open import Relation.Nullary.Decidable.Base
open import Path
open import Level

Discrete : Type a → Type a
\end{code}
%<*discrete-def>
\begin{code}
Discrete A = (x y : A) → Dec (x ≡ y)
\end{code}
%</discrete-def>
