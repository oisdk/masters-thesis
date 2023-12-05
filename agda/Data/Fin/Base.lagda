\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Fin.Base where

open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ; suc; zero)
open import Level
open import Data.Empty

module DisplayImpl where
 open import Data.Unit
 open import Data.Sum

 Fin : ℕ → Type₀
\end{code}
%<*fin-def-1>
\begin{code}
 Fin zero     = ⊥
\end{code}
%</fin-def-1>
%<*fin-def-2>
\begin{code}
 Fin (suc n)  = ⊤ ⊎ Fin n
\end{code}
%</fin-def-2>
\begin{code}

Fin : ℕ → Type₀
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern f0 = nothing
pattern fs n = just n
\end{code}
