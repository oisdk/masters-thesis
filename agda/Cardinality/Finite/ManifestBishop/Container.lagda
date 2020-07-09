\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.ManifestBishop.Container where

open import Prelude
open import Data.Fin
open import Container
open import Container.List public
open import Container.Membership (ℕ , Fin) public

ℬ : Type a → Type a
\end{code}
%<*bish-def>
\begin{code}
ℬ A = Σ[ support ⦂ List A ] ((x : A) → x ∈! support)
\end{code}
%</bish-def>
