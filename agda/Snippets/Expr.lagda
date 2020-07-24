\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Expr where

open import Prelude hiding (_⟨_⟩_; T; ⊤; tt)

module DataTop where
\end{code}
%<*data-top>
\begin{code}
  data ⊤ : Type₀ where
    tt : ⊤
\end{code}
%</data-top>
\begin{code}

open import Data.Unit
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
⟦ x ⟨ -′ ⟩ y ⟧ =
  do  x′ ← ⟦ x ⟧
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
%<*is-just>
\begin{code}
is-just : Maybe A → Bool
is-just nothing   = false
is-just (just _)  = true
\end{code}
%</is-just>
%<*tee>
\begin{code}
T : Bool → Type₀
T true   = ⊤
T false  = ⊥
\end{code}
%</tee>
%<*valid>
\begin{code}
Valid : Expr → Type₀
Valid e = T (is-just ⟦ e ⟧)
\end{code}
%</valid>
%<*static-eval>
\begin{code}
⟦_⟧! : (e : Expr) → { _ : Valid e } → ℕ
⟦ e ⟧! with ⟦ e ⟧
⟦ e ⟧! | just x = x
\end{code}
%</static-eval>
%<*example-eval>
\begin{code}
example-eval : Maybe ℕ
example-eval = ⟦ lit 4 ⟨ ×′ ⟩ lit 2 ⟧
\end{code}
%</example-eval>
%<*pair>
\begin{code}
record Pair (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  field
    fst  : A
    snd  : B
\end{code}
%</pair>
%<*example-static-eval>
\begin{code}
example-static-eval : ℕ
example-static-eval = ⟦ lit 4 ⟨ ×′ ⟩ lit 2 ⟧!
\end{code}
%</example-static-eval>
