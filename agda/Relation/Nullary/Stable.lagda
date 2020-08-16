\begin{code}
{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Stable where

open import Data.Empty
open import Level

Stable : Type a → Type a
\end{code}
%<*stable-def>
\begin{code}
Stable A = ¬ ¬ A → A
\end{code}
%</stable-def>
