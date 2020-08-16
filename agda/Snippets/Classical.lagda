\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Classical where

open import Prelude

doubleNeg-elim : Type a → Type a
doubleNeg-elim A =
\end{code}
%<*doubleneg-elim>
\begin{code}
  ¬ ¬ A → A
\end{code}
%</doubleneg-elim>
%<*classical-def>
\begin{code}
Classical : Type a → Type a
Classical A = ¬ ¬ A
\end{code}
%</classical-def>
%<*monad>
\begin{code}
pure : A → Classical A
pure x ¬x = ¬x x

_>>=_ : Classical A → (A → Classical B) → Classical B
¬¬x >>= f = λ ¬B → ¬¬x (λ x → f x ¬B)
\end{code}
%</monad>
\begin{code}
_<*>_ : Classical (A → B) → Classical A → Classical B
¬¬f <*> ¬¬x = λ ¬B → ¬¬x (λ x → ¬¬f (λ f → ¬B (f x)))

_>>_ : Classical A → Classical B → Classical B
_ >> x = x

\end{code}
%<*lem-proof>
\begin{code}
lem : Classical (A ⊎ (¬ A))
lem ¬lem = ¬lem (inr λ p → ¬lem (inl p))
\end{code}
%</lem-proof>
\begin{code}
