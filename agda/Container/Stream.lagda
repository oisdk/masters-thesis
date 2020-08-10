\begin{code}
{-# OPTIONS --cubical --safe #-}

module Container.Stream where

open import Prelude
open import Data.Fin
open import Container

Stream : Type a → Type a
\end{code}
%<*stream-def>
\begin{code}
Stream = ⟦ ⊤ , const ℕ ⟧
\end{code}
%</stream-def>
