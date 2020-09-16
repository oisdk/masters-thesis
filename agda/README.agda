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
  ; module IncorrectEval -- 2.7
  )


-- 2.4: Safe Evaluation with Maybe
import Data.Maybe using
  ( Maybe -- 2.8
  )

import Snippets.Maybe using
  ( maybe-two
  ; maybe-func)

import Snippets.Expr using
  ( _-_ -- 2.9
  ; ⟦_⟧
  )

import Data.Maybe.Sugar using
  ( pure
  ; _<*>_
  ; _>>=_ -- 2.10
  )

-- 2.5: Statically Proving the Evaluation is Safe

import Snippets.Expr using
  ( example-eval
  ; is-just)

import Data.Bool using
  (T)

import Data.Empty using
  (⊥)

import Snippets.Introduction using
  (⊤)

import Data.Empty using
  (¬_)

import Snippets.Expr using
  ( Pair -- 2.11
  ; Valid -- 2.12
  ; ⟦_⟧!
  ; example-static-eval -- 2.13
  )

import Snippets.Implicits using
  ( module Normal
  ; module ImplicitType -- 2.14
  )

-- 2.6: Equalities

import Snippets.Equality using
  ( module MLTTEquality -- 2.15
  ; sym
  )

-- 2.7: Some Proofs of Equality
import Snippets.Equality using
  ( refl -- 2.16
  )

import Snippets.Expr using
  (example-static-proof)

import Data.Nat.Properties using
  (+-assoc)

-- 2.8: Quotients

import Cubical.HITs.S1 using
  ( S¹ -- 2.17
  )

-- 2.9: Basic Type Formers

import Snippets.Formers using
  ( ℕ-or-String
  ; Pair
  ; fst
  ; snd
  ; pair
  )

import Data.Sigma using
  ( Σ
  ; _×_ -- 2.18
  )

import Data.Sum using
  ( _⊎_ -- 2.19
  )

-- 2.11: Comparing Classical and Constructive Proofs in Agda

import Snippets.Classical using
  ( Classical -- 2.20
  ; lem
  ; pure
  ; _>>=_
  )

import Relation.Nullary.Stable using
  (Stable)
