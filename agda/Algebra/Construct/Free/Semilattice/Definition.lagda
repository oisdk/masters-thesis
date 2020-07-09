\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Definition where

open import Prelude

infixr 5 _∷_
\end{code}
%<*kuratowski-def>
\begin{code}
data 𝒦 (A : Type a) : Type a where
  []   : 𝒦 A
  _∷_  : A → 𝒦 A → 𝒦 A
  com   : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  dup   : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
  trunc : isSet (𝒦 A)
\end{code}
%</kuratowski-def>
