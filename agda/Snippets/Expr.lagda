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
open import Data.Nat hiding (_∸_)
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
\begin{code}
module IncorrectEval where
  open import Data.Nat renaming (_∸_ to _-_)
\end{code}
%<*incorrect-eval>
\begin{code}
  ⟦_⟧ : Expr → ℕ
  ⟦ lit x ⟧ = x
  ⟦ xs ⟨ +′  ⟩ ys ⟧ = ⟦ xs ⟧ + ⟦ ys ⟧
  ⟦ xs ⟨ ×′  ⟩ ys ⟧ = ⟦ xs ⟧ * ⟦ ys ⟧
  ⟦ xs ⟨ -′  ⟩ ys ⟧ = ⟦ xs ⟧ - ⟦ ys ⟧
  ⟦ xs ⟨ ÷′  ⟩ ys ⟧ with ⟦ ys ⟧
  ⟦ xs ⟨ ÷′  ⟩ ys ⟧ | zero     = zero
  ⟦ xs ⟨ ÷′  ⟩ ys ⟧ | suc ys′  = ⟦ xs ⟧ ÷ suc ys′
\end{code}
%</incorrect-eval>
%<*safe-sub>
\begin{code}
_-_ : ℕ → ℕ → Maybe ℕ
n      - zero   = just n
suc n  - suc m  = n - m
zero   - suc m  = nothing
\end{code}
%</safe-sub>
\begin{code}
private
 module NoApplEval where
    ⟦_⟧ : Expr → Maybe ℕ
\end{code}
%<*add-helper>
\begin{code}
    ⟦ x ⟨ +′ ⟩ y ⟧ = add-helper ⟦ x ⟧ ⟦ y ⟧
      where
      add-helper : Maybe ℕ → Maybe ℕ → Maybe ℕ
      add-helper nothing   nothing   = nothing
      add-helper nothing   (just x)  = nothing
      add-helper (just x)  nothing   = nothing
      add-helper (just x)  (just y)  = just (x + y)
\end{code}
%</add-helper>
\begin{code}
    ⟦ _ ⟧ = nothing
private
 module ExplicitApplMonEval where
    ⟦_⟧ : Expr → Maybe ℕ
\end{code}
%<*add-helper-app>
\begin{code}
    ⟦ x ⟨ +′ ⟩ y ⟧ = pure _+_ <*> ⟦ x ⟧ <*> ⟦ y ⟧
\end{code}
%</add-helper-app>
%<*sub-bind>
\begin{code}
    ⟦ x ⟨ -′ ⟩ y ⟧ =
      ⟦ x  ⟧ >>= λ x′  →
      ⟦ y  ⟧ >>= λ y′  →
      x′ - y′
\end{code}
%</sub-bind>
\begin{code}
    ⟦ _ ⟧ = nothing
\end{code}
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
      x′ - y′
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
\begin{code}
module StaticEvalExplicit where
\end{code}
%<*static-eval-explicit>
\begin{code}
  ⟦_⟧! : (e : Expr) → Valid e → ℕ
  ⟦ e ⟧! v with ⟦ e ⟧
  ⟦ e ⟧! v | just x = x
\end{code}
%</static-eval-explicit>
\begin{code}
module StaticEvalRetrieve where
\end{code}
%<*retrieve-implicit>
\begin{code}
  ⟦_⟧! : (e : Expr) → { _ : Valid e } → ℕ
  ⟦ e ⟧! { valid } with ⟦ e ⟧
  ⟦ e ⟧! { valid } | just x = x
\end{code}
%</retrieve-implicit>
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
%<*example-static-proof>
\begin{code}
example-static-proof : ⟦ lit 4 ⟨ ×′ ⟩ lit 2 ⟧! ≡ 8
example-static-proof = refl
\end{code}
%</example-static-proof>
%<*quot-expr>
\begin{code}
data Expr/ : Type₀ where
  lit/ : ℕ → Expr/
  _⟪_⟫_ : Expr/ → Op → Expr/ → Expr/
  +-comm : ∀ x y → x ⟪ +′ ⟫ y ≡ y ⟪ +′ ⟫ x
  trunc/ : (x y : Expr/) → (p q : x ≡ y) → p ≡ q
\end{code}
%</quot-expr>
\begin{code}
m-+-comm : (x y : Maybe ℕ) → ⦇ x + y ⦈ ≡ ⦇ y + x ⦈
m-+-comm nothing nothing = refl
m-+-comm nothing (just x) = refl
m-+-comm (just x) nothing = refl
m-+-comm (just x) (just y) i = just (Data.Nat.Properties.+-comm x y i)

open import Data.Maybe.Properties

eval/ : Expr/ → Maybe ℕ
eval/ (lit/ x) = just x
eval/ (xs ⟪ +′ ⟫ ys) = ⦇ eval/ xs + eval/ ys ⦈
eval/ (xs ⟪ ×′ ⟫ ys) = ⦇ eval/ xs * eval/ ys ⦈
eval/ (xs ⟪ -′ ⟫ ys) =
  do  x′ ← eval/ xs
      y′ ← eval/ ys
      x′ - y′
eval/ (xs ⟪ ÷′ ⟫ ys) = do
  suc y′ ← eval/ ys
    where zero → nothing
  x′ ← eval/ xs
  guard (rem x′ (suc y′) ≟ 0)
  just (x′ ÷ suc y′)
eval/ (+-comm xs ys i) = m-+-comm (eval/ xs) (eval/ ys) i
eval/ (trunc/ x y p q i j) = Discrete→isSet (discreteMaybe Data.Nat.Properties.discreteℕ) (eval/ x) (eval/ y) (cong eval/ p) (cong eval/ q) i j
\end{code}
