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
  ( id
  )

import Snippets.Nat using
  ( ℕ -- 2.2
  ; add
  ; _-_ -- 2.3
  ; module NonCoveringSub
  ; _+_ -- 2.4
  ; module NonTermAdd
  )

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
  ; maybe-func
  )

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
  ; is-just
  )

import Data.Bool using
  ( T
  )

import Data.Empty using
  ( ⊥
  )

import Snippets.Introduction using
  ( ⊤
  )

import Data.Empty using
  ( ¬_
  )

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
  ( example-static-proof
  )

import Data.Nat.Properties using
  ( +-assoc
  )

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
  ( Stable
  )

------------------------------------------------------------------------
-- Chapter 3: Finiteness Predicates
------------------------------------------------------------------------

-- 3.1: Split Enumerability

import Cardinality.Finite.SplitEnumerable.Container using
  ( ℰ!
  )

import Container.List using
  ( List -- 3.1
  )

import Data.Fin.Base using
  (module DisplayImpl)

import Data.List using
  (List)

import Container using
  ( ⟦_⟧ -- 3.3
  )

import Container.Membership using
  ( _∈_ -- 3.4
  )

import Function.Fiber using
  ( fiber -- 3.5
  )

import Function.Surjective using
  ( SplitSurjective -- 3.6
  ; _↠!_
  )

import Cardinality.Finite.SplitEnumerable using
  ( ℰ!⇔Fin↠!
  )

import Data.Sigma.Properties using
  ( reassoc
  )

import Cardinality.Finite.SplitEnumerable using
  ( split-enum-is-split-surj
  ; ℰ!⟨2⟩ -- 3.7
  )

import Function.Surjective.Properties using
  ( ↠!-ident
  )

import Relation.Nullary.Discrete using
  ( Discrete
  )

import Snippets.Dec using
  ( Dec
  )

import Function.Injective using
  ( Injective
  ; _↣_
  )

import Function.Injective.Properties using
  (Discrete-pull-inj)

import Function.Surjective.Properties using
  ( surj-to-inj
  ; Discrete-distrib-surj
  )

import Cardinality.Finite.SplitEnumerable using
  (ℰ!⇒Discrete)

-- 3.2: Manifest Bishop Finiteness

import Cardinality.Finite.SplitEnumerable using
  ( module BoolSlop -- 3.8
  )

import HLevels using
  ( isContr -- 3.9
  )

import Container.Membership using
  ( _∈!_ -- 3.10
  )

import Cardinality.Finite.ManifestBishop.Container using
  ( ℬ
  )

import Snippets.Equivalence using
  ( isEquiv -- 3.11
  ; _≃_
  )

import Cardinality.Finite.ManifestBishop using
  ( ℬ⇔Fin≃
  )

-- 3.3: Cardinal Finiteness

import Cardinality.Finite.SplitEnumerable using
  ( ℰ!⟨2⟩
  ; ℰ!⟨2⟩′
  )

import HLevels using
  ( isProp -- 3.12
  )

import HITs.PropositionalTruncation using
  ( ∥_∥ -- 3.13
  ; rec -- 3.14
  )

import Cardinality.Finite.Cardinal using
  ( 𝒞
  ; 𝒞⇒Discrete
  )

import Relation.Nullary.Discrete.Properties using
  ( isPropDiscrete
  )

import HLevels using
  ( isSet -- 3.15
  )

import Relation.Nullary.Discrete.Properties using
  ( Discrete→isSet
  )

import HITs.PropositionalTruncation using
  ( rec→set -- 3.16
  )

import Cardinality.Finite.Cardinal using
  ( cardinality-is-unique
  )

import Data.List.Sort using
  ( insert
  ; sort
  ; sort-sorts
  ; sort-perm
  )

import Data.List.Relation.Binary.Permutation using
  ( _↭_
  )

import Data.List.Sort using
  ( sorted-perm-eq
  ; perm-invar
  )

import Cardinality.Finite.Cardinal using
  ( ¬⟨𝒞⋂ℬᶜ⟩
  )

import Snippets.Classical using
  ( classical-impl
  )

-- 3.4: Manifest Enumerability

import Cubical.HITs.S1 using
  ( S¹ -- 3.19
  )

import HLevels using
  ( isGroupoid -- 3.20
  )

import Cardinality.Finite.ManifestEnumerable.Container using
  ( ℰ
  )

import Cardinality.Finite.ManifestEnumerable using
  ( ℰ⟨S¹⟩
  )

import Cubical.HITs.S1 using
  ( isConnectedS¹
  )

import Function.Surjective using
  ( Surjective -- 3.21
  ; _↠_
  )

import Cardinality.Finite.ManifestEnumerable using
  (  ℰ⇔Fin↠
  )

import HITs.PropositionalTruncation.Properties using
  ( recompute -- 3.22
  )

-- 3.5: Kuratowski Finiteness

import Algebra.Construct.Free.Semilattice using
  ( 𝒦 -- 3.23
  )

import Algebra.Construct.Free.Semilattice.Direct using
  ( 𝒦
  )

import Algebra.Construct.Free.Semilattice.Relation.Unary.Membership using
  ( _∈_
  )

import Cardinality.Finite.Kuratowski using
  ( 𝒦ᶠ
  ; 𝒞⇔𝒦×Discrete -- 3.24
  )

------------------------------------------------------------------------
-- Chapter 4: Topos
------------------------------------------------------------------------

-- 4.1: Categories in HoTT

import Categories using
  ( PreCategory -- 4.1
  )

-- 4.2: The Category of Sets

import Categories.HSets using
  ( Ob
  )

-- 4.3: Closure

import Cardinality.Finite.SplitEnumerable using
  ( _|Σ|_
  ; sup-Σ
  )

import Cardinality.Finite.ManifestBishop using
  ( _|Π|_
  )

import Data.Tuple.UniverseMonomorphic using
  ( Tuple
  )

import Cardinality.Finite.Cardinal using
  ( _∥×∥_
  ; 𝒞⇒Choice
  )

-- 4.4: The Absence of the Subobject Classifier

import Snippets.Topos using
  ( Prop-univ
  ; prop-resize
  )

------------------------------------------------------------------------
-- Chapter 5: Search
------------------------------------------------------------------------

import Snippets.Bool using
  ( _∧_
  ; ∧-assoc -- 5.1
  ; some-assoc
  )

-- 5.1: How to make the Typechecker do Automation

import Snippets.Bool using
  ( obvious
  ; True
  ; toWitness
  ; extremely-obvious
  )

-- 5.2: Omniscience

import Relation.Nullary.Omniscience using
  ( Exhaustible
  ; Omniscient
  )

import Relation.Nullary.Decidable.Properties using
  ( Dec→DoubleNegElim
  )

import Relation.Nullary.Omniscience using
  ( Omniscient→Exhaustible
  )

import Cardinality.Finite.Kuratowski using
  ( 𝒦ᶠ⇒Exhaustible
  )

import Cardinality.Finite.ManifestEnumerable using
  ( ℰ⇒Omniscient
  )

import Relation.Nullary.Omniscience using
  ( Prop-Omniscient
  )

import Cardinality.Finite.Kuratowski using
  ( 𝒦ᶠ⇒Prop-Omniscient
  )

-- 5.3: An Interface for Proof Automation

import Cardinality.Finite.SplitEnumerable.Search using
  ( ∀?
  ; ∃?
  ; module PreInst
  )

import Snippets.Bool using
  ( module PreInst′
  )

import Cardinality.Finite.SplitEnumerable.Search using
  ( module WithInst
  )

import Snippets.Bool using
  ( ∧-idem -- 5.2
  ; module BadCurrying
  )

import Instance using
  ( it
  )

import Data.Product.NAry using
  ( Levels
  ; max-level
  ; Types
  ; ⦅_⦆⁺
  ; ⦅_⦆
  ; ArgForm
  ; _[_]→_
  ; [_$]
  ; Π[_$]
  ; ⦅_⦆[_]→_
  ; pi-arrs-plus
  ; Π[_^_$]
  )

import Cardinality.Finite.SplitEnumerable.Search using
  ( ∃?ⁿ
  ; ∃↯ⁿ
  )

import Snippets.Bool using
  ( ∧-comm
  )

-- 5.4: Countdown

import Countdown using
  ( ℰ!⟨Vec⟩
  ; ℰ!⟨Op⟩
  ; module WrongPerm
  ; module IsoPerm
  ; Perm
  ; ℰ!⟨Perm⟩
  )

import Dyck using
  ( Dyck
  ; module NonParamTree
  )

import Countdown using
  ( ExprTree
  ; Transformation
  ; ℰ!⟨ExprTree⟩
  ; ℰ!⟨Transformation⟩
  ; eval
  ; _!⟨_⟩!_
  ; Solution
  ; exampleSolutions
  )
