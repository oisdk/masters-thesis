\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Topos where

open import Prelude

\end{code}
%<*prop-univ>
\begin{code}
Prop-univ : Type₁
Prop-univ = Σ[ t ⦂ Type₀ ] isProp t
\end{code}
%</prop-univ>
\begin{code}
prop-resize : (u : Level) → Type (ℓsuc (ℓsuc u))
prop-resize u =
\end{code}
%<*prop-resize>
\begin{code}
  Σ[ t ⦂ Type u ] isProp t ≃ Σ[ t ⦂ Type (ℓsuc u) ] isProp t
\end{code}
%</prop-resize>
