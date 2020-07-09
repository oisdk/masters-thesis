\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestEnumerable.Container where

open import Prelude
open import Data.Fin
open import Container
open import Container.List public
open import Container.Membership (ℕ , Fin) public

ℰ : Type a → Type a
\end{code}
%<*manifest-enum-def>
\begin{code}
ℰ A = Σ[ support ⦂ List A ] ((x : A) → ∥ x ∈ support ∥)
\end{code}
%</manifest-enum-def>
