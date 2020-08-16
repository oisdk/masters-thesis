\begin{code}
module Snippets.Nat where

open import Level
\end{code}
%<*nat-def>
\begin{code}
data ℕ : Type₀ where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat-def>
\begin{code}
{-# BUILTIN NATURAL ℕ #-}

private
  module TextAdd where
\end{code}
%<*text-add>
\begin{code}
    add : ℕ → ℕ → ℕ
    add zero     m = m
    add (suc n)  m = suc (add n m)
\end{code}
%</text-add>
\begin{code}
private
 module BadSub where
  {-# NON_COVERING #-}
\end{code}
%<*bad-sub>
\begin{code}
  _-_ : ℕ → ℕ → ℕ
  n      - zero  = zero
  suc n  - suc m = n - m
\end{code}
%</bad-sub>
%<*sub-fix>
\begin{code}
infixl 6 _-_
\end{code}
%</sub-fix>
%<*sub-def>
\begin{code}
_-_ : ℕ → ℕ → ℕ
n      - zero   = zero
suc n  - suc m  = n - m
zero   - suc m  = zero
\end{code}
%</sub-def>
\begin{code}
private
 module BadAdd where
  {-# TERMINATING #-}
\end{code}
%<*bad-add>
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero  + m = m
  n     + m = suc ((n - 1) + m)
\end{code}
%</bad-add>
%<*add-def>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero   + m = m
suc n  + m = suc (n + m)
\end{code}
%</add-def>
\begin{code}
RiemannIsTrue : Type₀
RiemannIsTrue = ℕ

{-# NON_TERMINATING #-}
\end{code}
%<*riemann-proof>
\begin{code}
riemann-proof : RiemannIsTrue
riemann-proof = riemann-proof
\end{code}
%</riemann-proof>

