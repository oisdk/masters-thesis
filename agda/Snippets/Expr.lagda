\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Expr where

open import Prelude hiding (_⟨_⟩_)
open import Data.Maybe
open import Data.Maybe.Sugar
open import Data.Nat renaming (_∸_ to _-_)
open import Data.Nat.Properties using () renaming (_≤ᴮ_ to _≤_; _≡ᴮ_ to _≟_)

data Op : Type₀ where
  +′ ×′ -′ ÷′ : Op

data Expr : Type₀ where
  lit : ℕ → Expr
  _⟨_⟩_ : Expr → Op → Expr → Expr

⟦_⟧ : Expr → Maybe ℕ
⟦ lit x ⟧ = just x
⟦ x ⟨ +′ ⟩ y ⟧ = ⦇ ⟦ x ⟧ + ⟦ y ⟧ ⦈
⟦ x ⟨ ×′ ⟩ y ⟧ = ⦇ ⟦ x ⟧ * ⟦ y ⟧ ⦈
⟦ x ⟨ -′ ⟩ y ⟧ = do
  x′ ← ⟦ x ⟧
  y′ ← ⟦ y ⟧
  guard (y′ ≤ x′)
  just (x′ - y′)
⟦ x ⟨ ÷′ ⟩ y ⟧ = do
  suc y′ ← ⟦ y ⟧
    where zero → nothing
  x′ ← ⟦ x ⟧
  guard (rem x′ (suc y′) ≟ 0)
  just (x′ ÷ suc y′)

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
