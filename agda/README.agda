{-# OPTIONS --cubical #-}

module README where

------------------------------------------------------------------------
-- Chapter 2: Programming and Proving in Cubical Agda
------------------------------------------------------------------------

-- 2.1: Basic Functional Programming in Agda
import Snippets.Bool using
  ( Bool -- 2.1
  ; Boolean
  ; a-boolean)

-- 2.2: Some Functions
import Snippets.Bool using
  ( not
  ; module LambdaNot)
import Function using
  (id)
import Snippets.Nat using
  ( ℕ -- 2.2
  ; add
  ; _-_ -- 2.3
  ; module NonCoveringSub
  ; _+_ -- 2.4
  ; module NonTermAdd)

-- 2.3: An Expression Evaluator
import Snippets.Expr using
  ( Op -- 2.5
  ; Expr -- 2.6
  ; ⟦_⟧ -- 2.7
  )
