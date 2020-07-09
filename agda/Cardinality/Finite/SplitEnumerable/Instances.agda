{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable.Instances where

open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.ManifestBishop using (_|Π|_)
open import Data.Fin
open import Prelude
open import Data.List.Membership
open import Data.Tuple

import Data.Unit.UniversePolymorphic as Poly

private
  infixr 4 _?×_
  data _?×_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
    pair : A → B → A ?× B

instance
  poly-inst : ∀ {a} → Poly.⊤ {a}
  poly-inst = Poly.tt

module _ {a b} {A : Type a} (B : A → Type b) where
  Im-Type : (xs : List A) → Type (a ℓ⊔ b)
  Im-Type = foldr (λ x xs → ℰ! (B x) ?× xs) Poly.⊤

  Tup-Im-Lookup : ∀ x (xs : List A) → x ∈ xs → Im-Type xs → ℰ! (B x)
  Tup-Im-Lookup x (y ∷ xs) (f0   , y≡x ) (pair ℰ!⟨Bx⟩ _) = subst (ℰ! ∘ B) y≡x ℰ!⟨Bx⟩
  Tup-Im-Lookup x (y ∷ xs) (fs n , x∈ys) (pair _ tup) = Tup-Im-Lookup x xs (n , x∈ys) tup

  Tup-Im-Pi : (xs : ℰ! A) → Im-Type (xs .fst) → ∀ x → ℰ! (B x)
  Tup-Im-Pi xs tup x = Tup-Im-Lookup x (xs .fst) (xs .snd x) tup

instance
  inst-pair : ⦃ lhs : A ⦄ ⦃ rhs : B ⦄ → A ?× B
  inst-pair ⦃ lhs ⦄ ⦃ rhs ⦄ = pair lhs rhs

instance
  fin-sigma : ⦃ lhs : ℰ! A ⦄ {B : A → Type b} → ⦃ rhs : Im-Type B (lhs .fst) ⦄ → ℰ! (Σ A B)
  fin-sigma ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |Σ| Tup-Im-Pi _ lhs rhs

instance
  fin-pi : ⦃ lhs : ℰ! A ⦄ {B : A → Type b} → ⦃ rhs : Im-Type B (lhs .fst) ⦄ → (ℰ! ((x : A) → B x))
  fin-pi ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |Π| Tup-Im-Pi _ lhs rhs

-- instance
--   fin-prod : ⦃ lhs : ℰ! A ⦄ ⦃ rhs : ℰ! B ⦄ → ℰ! (A × B)
--   fin-prod ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |×| rhs

-- instance
--   fin-fun : {A B : Type₀} ⦃ lhs : ℰ! A ⦄ ⦃ rhs : ℰ! B ⦄ → ℰ! (A → B)
--   fin-fun ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |Π| λ _ → rhs

instance
  fin-sum : ⦃ lhs : ℰ! A ⦄ ⦃ rhs : ℰ! B ⦄ → ℰ! (A ⊎ B)
  fin-sum ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |⊎| rhs


instance
  fin-bool : ℰ! Bool
  fin-bool = ℰ!⟨2⟩

instance
  fin-top : ℰ! ⊤
  fin-top = ℰ!⟨⊤⟩

instance
  fin-bot : ℰ! ⊥
  fin-bot = ℰ!⟨⊥⟩

instance
  fin-fin : ∀ {n} → ℰ! (Fin n)
  fin-fin  = ℰ!⟨Fin⟩
