\begin{code}
{-# OPTIONS --safe --without-K #-}

module Level where

open import Agda.Primitive
  using (Level)
  renaming ( _⊔_ to _ℓ⊔_
           ; lzero to ℓzero
           ; lsuc  to ℓsuc
           ; Set to Type )
  public


\end{code}
%<*level-var-decl>
\begin{code}
variable
  a b c : Level
  A  : Type a
  B  : Type b
  C  : Type c
\end{code}
%</level-var-decl>
