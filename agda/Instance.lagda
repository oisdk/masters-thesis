\begin{code}
{-# OPTIONS --without-K --safe #-}

module Instance where

open import Level

\end{code}
%<*it-def>
\begin{code}
it : ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x
\end{code}
%</it-def>
\begin{code}
