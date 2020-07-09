{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable.Inductive where

open import Data.List public
open import Data.List.Membership
open import Prelude

ℰ! : Type a → Type a
ℰ! A = Σ[ xs ⦂ List A ] ((x : A) → x ∈ xs)
