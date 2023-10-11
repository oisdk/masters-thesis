\begin{code}
{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Display where

open import Prelude
open import Cubical.HITs.PropositionalTruncation hiding (rec)
import Cubical.HITs.PropositionalTruncation as Cubical

\end{code}
%<*rec-prop-trunc>
\begin{code}[number=elim-prop]
rec : isProp B → (A → B) → ∥ A ∥ → B
\end{code}
%</rec-prop-trunc>
%<*rec-prop-trunc-set>
\begin{code}[number=elim-prop-coh]
rec→set : isSet B → (f : A → B) → (∀ x y → f x ≡ f y) → ∥ A ∥ → B
\end{code}
%</rec-prop-trunc-set>
\begin{code}
rec = Cubical.rec
rec→set isSetB = rec→Set isSetB
\end{code}
