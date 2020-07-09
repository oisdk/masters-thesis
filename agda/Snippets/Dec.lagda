\begin{code}
{-# OPTIONS --cubical --safe #-}
module Snippets.Dec where

open import Level
open import Data.Empty
\end{code}
%<*dec-def>
\begin{code}
data Dec (A : Type a) : Type a where
  yes  :    A → Dec A
  no   : ¬  A → Dec A
\end{code}
%</dec-def>
