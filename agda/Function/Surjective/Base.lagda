\begin{code}
{-# OPTIONS --cubical --safe #-}

module Function.Surjective.Base where

open import Path
open import Function.Fiber
open import Level
open import HITs.PropositionalTruncation
open import Data.Sigma

Surjective : (A → B) → Type _
\end{code}
%<*surjective>
\begin{code}
Surjective f = ∀ y → ∥ fiber f y ∥
\end{code}
%</surjective>
\begin{code}
SplitSurjective : (A → B) → Type _
\end{code}
%<*split-surjective>
\begin{code}
SplitSurjective f = ∀ y → fiber f y
\end{code}
%</split-surjective>
\begin{code}

infixr 0 _↠!_ _↠_

_↠!_ : Type a → Type b → Type (a ℓ⊔ b)
\end{code}
%<*split-surjection>
\begin{code}
A ↠! B = Σ (A → B) SplitSurjective
\end{code}
%</split-surjection>
\begin{code}
_↠_ : Type a → Type b → Type (a ℓ⊔ b)
\end{code}
%<*surjection>
\begin{code}
A ↠ B = Σ (A → B) Surjective
\end{code}
%</surjection>
