\begin{code}
{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Discrete.Properties where

open import Relation.Nullary.Discrete.Base
open import Relation.Nullary.Stable.Properties using (Stable≡→isSet)
open import Relation.Nullary.Decidable.Properties using (Dec→Stable; isPropDec)

open import HLevels
open import Level
open import Path

Discrete→isSet :
\end{code}
%<*discrete-isset>
\begin{code}
  Discrete A → isSet A
\end{code}
%</discrete-isset>
\begin{code}
Discrete→isSet d = Stable≡→isSet (λ x y → Dec→Stable (x ≡ y) (d x y))

isPropDiscrete :
\end{code}
%<*is-prop-discrete>
\begin{code}
  isProp (Discrete A)
\end{code}
%</is-prop-discrete>
\begin{code}
isPropDiscrete f g i x y = isPropDec (Discrete→isSet f x y) (f x y) (g x y) i
\end{code}
