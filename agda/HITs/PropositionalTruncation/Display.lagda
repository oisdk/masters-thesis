\begin{code}
{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Display where

open import Prelude
open import Cubical.HITs.PropositionalTruncation
\end{code}
%<*rec-prop-trunc>
\begin{code}
rec : isProp B → (A → B) → ∥ A ∥ → B
\end{code}
%</rec-prop-trunc>
%<*rec-prop-trunc-set>
\begin{code}
rec→set : isSet B → (f : A → B) → (∀ x y → f x ≡ f y) → ∥ A ∥ → B
\end{code}
%</rec-prop-trunc-set>
\begin{code}
rec = recPropTrunc
rec→set isSetB = recPropTrunc→Set isSetB
\end{code}
