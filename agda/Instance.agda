{-# OPTIONS --without-K --safe #-}

module Instance where

open import Level

it : ∀ {a} {A : Type a} → ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x
