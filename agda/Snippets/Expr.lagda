\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Expr where

open import Prelude hiding (_⟨_⟩_)
open import Data.Maybe
open import Data.Maybe.Sugar
open import Data.Nat renaming (_∸_ to _-_)
open import Data.Nat.Properties using () renaming (_≤ᴮ_ to _≤_; _≡ᴮ_ to _≟_)

\end{code}
%<*op-def>
\begin{code}
data Op : Type₀ where
  +′  : Op
  ×′  : Op
  -′  : Op
  ÷′  : Op
\end{code}
%</op-def>
%<*expr-def>
\begin{code}
data Expr : Type₀ where
  lit : ℕ → Expr
  _⟨_⟩_ : Expr → Op → Expr → Expr
\end{code}
%</expr-def>
\begin{code}
_ : Expr
_ =
\end{code}
%<*example-expr>
\begin{code}
  lit 4 ⟨ +′ ⟩ lit 5
\end{code}
%</example-expr>
%<*eval-ty>
\begin{code}
⟦_⟧ : Expr → Maybe ℕ
\end{code}
%</eval-ty>
%<*lit-case>
\begin{code}
⟦ lit x ⟧ = just x
\end{code}
%</lit-case>
%<*appl-cases>
\begin{code}
⟦ x ⟨ +′  ⟩ y ⟧ = ⦇ ⟦ x ⟧ +  ⟦ y ⟧ ⦈
⟦ x ⟨ ×′  ⟩ y ⟧ = ⦇ ⟦ x ⟧ *  ⟦ y ⟧ ⦈
\end{code}
%</appl-cases>
%<*sub-case>
\begin{code}
⟦ x ⟨ -′ ⟩ y ⟧ = do
  x′ ← ⟦ x ⟧
  y′ ← ⟦ y ⟧
  guard (y′ ≤ x′)
  just (x′ - y′)
\end{code}
%</sub-case>
%<*div-case>
\begin{code}
⟦ x ⟨ ÷′ ⟩ y ⟧ = do
  suc y′ ← ⟦ y ⟧
    where zero → nothing
  x′ ← ⟦ x ⟧
  guard (rem x′ (suc y′) ≟ 0)
  just (x′ ÷ suc y′)
\end{code}
%</div-case>
\begin{code}

IsJust : Maybe A → Type₀
IsJust nothing  = ⊥
IsJust (just _) = ⊤

Valid : Expr → Type₀
Valid e = IsJust ⟦ e ⟧

from-just : (j : Maybe A) → { _ : IsJust j } → A
from-just (just x) = x

⟦_⟧! : (e : Expr) → { _ : Valid e } → ℕ
⟦ e ⟧! { valid } = from-just ⟦ e ⟧ { valid }
\end{code}
