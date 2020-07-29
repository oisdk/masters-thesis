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
