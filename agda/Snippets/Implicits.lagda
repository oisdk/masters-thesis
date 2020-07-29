\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Implicits where

open import Level

module Normal where
\end{code}
%<*id-def>
\begin{code}
  id : A → A
  id x = x
\end{code}
%</id-def>
\begin{code}
module ImplicitType where
\end{code}
%<*id-expl>
\begin{code}
  id : ∀ {a} {A : Type a} → A → A
  id {a} {A} x = x
\end{code}
%</id-expl>
