{-# OPTIONS --cubical --safe #-}

module Data.Empty.Base where

open import Cubical.Data.Empty
  using (⊥; isProp⊥)
  public
open import Level

infix 4.5 ¬_
¬_ : Type a → Type a
¬ A = A → ⊥

⊥-elim : ⊥ → A
⊥-elim ()
