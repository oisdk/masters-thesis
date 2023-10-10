\begin{code}
{-# OPTIONS --safe --cubical #-}

open import Container

module Container.Membership {s p} (𝒞 : Container s p) where

open import Prelude
open import HLevels

infixr 5 _∈_ _∈!_
_∈_ : A → ⟦ 𝒞 ⟧ A → Type _
\end{code}
%<*membership-def>
\begin{code}[number=container-membership]
x ∈ xs = fiber (snd xs) x
\end{code}
%</membership-def>
\begin{code}

_∈!_ : A → ⟦ 𝒞 ⟧ A → Type _
\end{code}
%<*uniq-memb-def>
\begin{code}[number=uniq-memb-def]
x ∈! xs = isContr (x ∈ xs)
\end{code}
%</uniq-memb-def>
