{-# OPTIONS --cubical #-}

module README where

------------------------------------------------------------------------
-- Chapter 2: Programming and Proving in Cubical Agda
------------------------------------------------------------------------

-- 2.1: Basic Functional Programming in Agda
import Snippets.Bool using (Bool; false; true; Boolean; a-boolean)

-- 2.2: Some Functions
import Snippets.Bool using (not; module LambdaNot)
import Function using (id)
import Snippets.Nat using (ℕ; add; _-_; module NonCoveringSub)
