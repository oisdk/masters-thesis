\begin{code}
{-# OPTIONS --cubical --safe #-}

module Container.List where

open import Prelude
open import Data.Fin
open import Container

List : Type a → Type a
\end{code}
%<*list-def>
\begin{code}[number=list-def]
List = ⟦ ℕ , Fin ⟧
\end{code}
%</list-def>
