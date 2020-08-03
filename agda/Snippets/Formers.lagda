\begin{code}
{-# OPTIONS --cubical #-}


module Snippets.Formers where

open import Prelude hiding (fst; snd; _×_)
open import Agda.Builtin.String
\end{code}
%<*pair-def>
\begin{code}
Pair : Type a → Type a → Type a
Pair A B = (x : Bool) → if x then A else B
\end{code}
%</pair-def>
%<*fst-def>
\begin{code}
fst : Pair A B → A
fst x = x true
\end{code}
%</fst-def>
%<*snd-def>
\begin{code}
snd : Pair A B → B
snd x = x false
\end{code}
%</snd-def>
%<*mk-pair>
\begin{code}
pair : A → B → Pair A B
pair x y true   = x
pair x y false  = y
\end{code}
%</mk-pair>
%<*nat-or-string>
\begin{code}
ℕ-or-String : (x : Bool) → if x then ℕ else String
ℕ-or-String true   = 1
ℕ-or-String false  = "It was false!"
\end{code}
%</nat-or-string>
%<*pair-sigma>
\begin{code}
_×_ : Type a → Type b → Type (a ℓ⊔ b)
A × B = Σ A λ _ → B
\end{code}
%</pair-sigma>
