\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Relation.Nullary.Omniscience where

open import Prelude
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic
open import Relation.Nullary
open import Data.Bool using (bool)

private
  variable
    p : Level
    P : A → Type p


Omniscient Exhaustible Prop-Omniscient : ∀ p {a} → Type a → Type _
\end{code}
%<*omniscient>
\begin{code}
Omniscient p A = ∀ {P : A → Type p} → (∀ x → Dec (P x)) → Dec (∃[ x ] P x)
\end{code}
%</omniscient>
%<*exhaustible>
\begin{code}
Exhaustible p A = ∀ {P : A → Type p} → (∀ x → Dec (P x)) → Dec (∀ x → P x)
\end{code}
%</exhaustible>
%<*omniscient-to-exhaustible>
\begin{code}
Omniscient→Exhaustible : Omniscient p A → Exhaustible p A
Omniscient→Exhaustible omn P? =
  map-dec
    (λ ¬∃P x → Dec→DoubleNegElim _ (P? x) (¬∃P ∘ (x ,_)))
    (λ ¬∃P ∀P → ¬∃P λ p → p .snd (∀P (p .fst)))
    (! (omn (! ∘ P?)))
\end{code}
%</omniscient-to-exhaustible>
%<*prop-omniscient>
\begin{code}
Prop-Omniscient p A = ∀ {P : A → Type p} → (∀ x → Dec (P x)) → Dec ∥ ∃[ x ] P x ∥
\end{code}
%</prop-omniscient>
