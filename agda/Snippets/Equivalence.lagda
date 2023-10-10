\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Equivalence where

open import Level
open import Data.Sigma
open import HLevels
open import Cubical.Foundations.Equiv using (fiber)

module _ {A : Type a} {B : Type b} where
  isEquiv : (A → B) → Type _
\end{code}
%<*is-equiv-def>
\begin{code}
  isEquiv f = ∀ y → isContr (fiber f y)
\end{code}
%</is-equiv-def>
\begin{code}
_≃_ : Type a → Type b → Type _
\end{code}
%<*equiv-def>
\begin{code}[number=equiv-def]
A ≃ B = Σ[ f ⦂ (A → B) ] isEquiv f
\end{code}
%</equiv-def>
