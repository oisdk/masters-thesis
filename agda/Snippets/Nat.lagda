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
_-_ : ℕ → ℕ → ℕ
n     - zero  = zero
zero  - suc m = zero
suc n - suc m = n - m
\end{code}
