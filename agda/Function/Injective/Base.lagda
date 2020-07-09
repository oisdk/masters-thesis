\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Function.Injective.Base where

open import Level
open import Path
open import Data.Sigma

Injective : (A → B) → Type _
\end{code}
%<*injective>
\begin{code}
Injective f = ∀ x y → f x ≡ f y → x ≡ y
\end{code}
%</injective>
\begin{code}

infixr 0 _↣_
_↣_ : Type a → Type b → Type (a ℓ⊔ b)
\end{code}
%<*injection>
\begin{code}
A ↣ B = Σ[ f ⦂ (A → B) ] Injective f
\end{code}
%</injection>
\begin{code}
refl-↣ : A ↣ A
refl-↣ .fst x = x
refl-↣ .snd x y x≡y = x≡y
\end{code}
