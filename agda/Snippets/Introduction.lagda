\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Introduction where

open import Level
open import Path
\end{code}
%<*bot>
\begin{code}
data ⊥ : Type₀ where
\end{code}
%</bot>
%<*top>
\begin{code}
record ⊤ : Type₀ where
  constructor tt
\end{code}
%</top>
%<*bool>
\begin{code}
data Bool : Type₀ where
  true   : Bool
  false  : Bool
\end{code}
%</bool>
\begin{code}
if_then_else_ : Bool → A → A → A
if true  then t else f = t
if false then t else f = f
\end{code}
%<*sigma>
\begin{code}
record Σ (A : Type a) (B : A → Type b) : Type (a ℓ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
\end{code}
%</sigma>
\begin{code}
∃ : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃ {A = A} = Σ A

infixr 4.5 ∃-syntax
∃-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → e) = ∃[ x ] e

infixr 4.5 Σ⦂-syntax
Σ⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ⦂-syntax = Σ

syntax Σ⦂-syntax t (λ x → e) = Σ[ x ⦂ t ] e

module SigmaSyntaxes {a b} {A : Type a} {B : A → Type b} where
  example₁ : Type _
  example₁ =
\end{code}
%<*sigma-syntax-1>
\begin{code}[inline]
    Σ A B
\end{code}
%</sigma-syntax-1>
\begin{code}
  example₂ : Type _
  example₂ =
\end{code}
%<*sigma-syntax-2>
\begin{code}[inline]%
    ∃ B
\end{code}
%</sigma-syntax-2>
\begin{code}
  example₃ : Type _
\end{code}
\begin{code}
  example₃ =
\end{code}
%<*sigma-syntax-3>
\begin{code}[inline]
    Σ[ x ⦂ A ] B x
\end{code}
%</sigma-syntax-3>
\begin{code}
  example₄ =
\end{code}
%<*sigma-syntax-4>
\begin{code}
    ∃[ x ] B x
\end{code}
%</sigma-syntax-4>
\begin{code}

Π : (A : Type a) (B : A → Type b) → Type _
Π A B = (x : A) → B x

∀′ : {A : Type a} (B : A → Type b) → Type _
∀′ {A = A} B = Π A B

infixr 4.5 ∀-syntax
∀-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∀-syntax = ∀′

syntax ∀-syntax (λ x → e) = ∀[ x ] e

infixr 4.5 Π⦂-syntax
Π⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Π⦂-syntax = Π

syntax Π⦂-syntax t (λ x → e) = Π[ x ⦂ t ] e

module PiSyntaxes {a b} {A : Type a} {B : A → Type b} where
  example₁ : Type _
  example₁ =
\end{code}
%<*pi-syntax-1>
\begin{code}
    Π A B
\end{code}
%</pi-syntax-1>
\begin{code}
  example₂ : Type _
  example₂ =
\end{code}
%<*pi-syntax-2>
\begin{code}
    (x : A) → B x
\end{code}
%</pi-syntax-2>
\begin{code}
  example₃ : Type _
\end{code}
\begin{code}
  example₃ =
\end{code}
%<*pi-syntax-3>
\begin{code}[inline]
    ∀ x → B x
\end{code}
%</pi-syntax-3>
\begin{code}
module SigmaDisjUnion where
  _⊎_ : Type a → Type a → Type _
\end{code}
%<*sigma-disj-union>
\begin{code}
  A ⊎ B = Σ[ x ⦂ Bool ] if x then A else B
\end{code}
%</sigma-disj-union>
%<*disj-union>
\begin{code}
data _⊎_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inl  : A  → A ⊎ B
  inr  : B  → A ⊎ B
\end{code}
%</disj-union>
\begin{code}
isContr : Type a → Type a
isProp : Type a → Type a
isSet : Type a → Type a
isGroupoid : Type a → Type a
\end{code}
%<*isContr>
\begin{code}[number=isContr]
isContr A = Σ[ x ⦂ A ] ∀ y → x ≡ y
\end{code}
%</isContr>
%<*isProp>
\begin{code}[number=isProp]
isProp A = (x y : A) → x ≡ y
\end{code}
%</isProp>
%<*isSet>
\begin{code}
isSet A = (x y : A) → isProp (x ≡ y)
\end{code}
%</isSet>
%<*isGroupoid>
\begin{code}
isGroupoid A = (x y : A) → isSet (x ≡ y)
\end{code}
%</isGroupoid>
%<*fiber>
\begin{code}
fiber : (A → B) → B → Type _
fiber f y = ∃[ x ] (f x ≡ y)
\end{code}
%</fiber>
%<*not>
\begin{code}
¬_ : Type a → Type a
¬ A = A → ⊥
\end{code}
%</not>
