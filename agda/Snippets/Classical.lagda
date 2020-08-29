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
open import Cardinality.Finite.Cardinal using (𝒞; ¬⟨𝒞⋂ℬᶜ⟩)
open import Cardinality.Finite.ManifestBishop.Inductive using (ℬ)

module _ {A : Type a} { B : Type b} where
\end{code}
%<*classical-impl>
\begin{code}
  classical-impl : ¬ (A × ¬ B) → Classical (A → B)
  classical-impl ¬A×¬B = do
    A? ← lem {A = A}
    B? ← lem {A = B}
    case (A? , B?) of
      λ { (inl  a   , inl   b   ) → pure (const b)
        ; (inl  a   , inr   ¬b  ) → ⊥-elim (¬A×¬B (a , ¬b))
        ; (inr  ¬a  , inl   b   ) → pure (const b)
        ; (inr  ¬a  , inr   ¬b  ) → pure (λ x → ⊥-elim (¬a x))
        }
\end{code}
%</classical-impl>
