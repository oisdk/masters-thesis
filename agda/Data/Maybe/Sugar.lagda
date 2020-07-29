\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Sugar where

open import Prelude
open import Data.Maybe

infixl 4 _<*>_

_>>=_ : Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x >>= f = f x

\end{code}
%<*pure>
\begin{code}
pure : A → Maybe A
pure = just
\end{code}
%</pure>
%<*ap>
\begin{code}
_<*>_ :  Maybe (A → B) →
         Maybe A →
         Maybe B
nothing   <*> xs       = nothing
just f    <*> nothing  = nothing
just f    <*> just x   = just (f x)
\end{code}
%</ap>
\begin{code}
_>>_ : Maybe A → Maybe B → Maybe B
nothing >> _ = nothing
just _  >> y = y

guard : Bool → Maybe ⊤
guard false = nothing
guard true  = just tt
\end{code}
