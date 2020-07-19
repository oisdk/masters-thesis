\begin{code}
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Snippets.Interactive where

open import Prelude
open import Data.List hiding (_++_)

infixr 5 _++_
_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

module Step1 where
\end{code}
%<*step1>
\begin{code}
  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc = {!!}
\end{code}
%</step1>
\begin{code}
module Step2 where
\end{code}
%<*step2>
\begin{code}
  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc xs ys zs = {!!}
\end{code}
%</step2>
\begin{code}
module Step3 where
\end{code}
%<*step3>
\begin{code}
  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []        ys zs = refl
  ++-assoc (x ∷ xs)  ys zs = cong (x ∷_) (++-assoc xs ys zs)
\end{code}
%</step3>
