\begin{code}
{-# OPTIONS --cubical #-}

module Snippets.Maybe where

open import Prelude
open import Data.Maybe
\end{code}
%<*maybe-two>
\begin{code}
maybe-two : Maybe ℕ
maybe-two = just 2
\end{code}
%</maybe-two>
%<*maybe-nat-to-nat>
\begin{code}
maybe-func : Maybe (ℕ → ℕ)
maybe-func = nothing
\end{code}
%</maybe-nat-to-nat>
