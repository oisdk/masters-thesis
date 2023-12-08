{-# OPTIONS --cubical --safe #-}

module README where

------------------------------------------------------------------------
-- Section 2: Finiteness Predicates
------------------------------------------------------------------------

-- 2.1: Split Enumerability

import Cardinality.Finite.SplitEnumerable.Container using
  ( ℰ!
  )

import Container using
  ( ⟦_⟧
  )

import Data.List using
  (List)

import Container.List using
  ( List
  )

import Data.Fin.Base using
  (module DisplayImpl)

import Function.Fiber using
  ( fiber
  )

import Container.Membership using
  ( _∈_
  )

import Function.Surjective using
  ( SplitSurjective
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
  ; ℰ!⟨2⟩
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

-- 2.2: Manifest Bishop Finiteness

import Cardinality.Finite.SplitEnumerable using
  ( module BoolSlop
  )

import HLevels using
  ( isContr
  )

import Container.Membership using
  ( _∈!_
  )

import Cardinality.Finite.ManifestBishop.Container using
  ( ℬ
  )

import Data.List.Membership using
  ( uniques
  ; _\\_
  )

import Snippets.Equivalence using
  ( isEquiv
  ; _≃_
  )

import Cardinality.Finite.ManifestBishop using
  ( ℬ⇔Fin≃
  )

-- 2.3: Cardinal Finiteness

import HLevels using
  ( isProp
  )

import HITs.PropositionalTruncation using
  ( ∥_∥
  ; rec
  )

import Cardinality.Finite.Cardinal using
  ( 𝒞
  ; 𝒞⇒Discrete
  )

import Relation.Nullary.Discrete.Properties using
  ( isPropDiscrete
  )

import HLevels using
  ( isSet
  )

import Relation.Nullary.Discrete.Properties using
  ( Discrete→isSet
  )

import HITs.PropositionalTruncation using
  ( rec→set
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
  ; 𝒞⇒ℬ
  )

-- 2.4: Manifest Enumerability

import Cubical.HITs.S1 using
  ( S¹
  )

import HLevels using
  ( isGroupoid
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
  ( Surjective
  ; _↠_
  )

import Cardinality.Finite.ManifestEnumerable using
  (  ℰ⇔Fin↠
  )

import HITs.PropositionalTruncation.Properties using
  ( recompute
  )

-- 2.5: Kuratowski Finiteness

import Algebra.Construct.Free.Semilattice using
  ( 𝒦
  )

import Algebra.Construct.Free.Semilattice.Direct using
  ( 𝒦
  )

import Algebra.Construct.Free.Semilattice.Relation.Unary.Membership using
  ( _∈_
  )

import Cardinality.Finite.Kuratowski using
  ( 𝒦ᶠ
  ; 𝒞⇔𝒦×Discrete
  )

------------------------------------------------------------------------
-- Section 3: Topos
------------------------------------------------------------------------

-- 3.1: Categories in HoTT

import Categories using
  ( PreCategory
  )

-- 3.2: The Category of Sets

import Categories.HSets using
  ( Ob
  )

-- 3.3: Closure

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

------------------------------------------------------------------------
-- Section 4: Search
------------------------------------------------------------------------

import Snippets.Bool using
  ( _∧_
  ; ∧-assoc
  ; some-assoc
  )

-- 4.1: How to make the Typechecker do Automation

import Snippets.Bool using
  ( obvious
  ; True
  ; toWitness
  ; extremely-obvious
  )

-- 4.2: Omniscience

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

-- 4.3: An Interface for Proof Automation

import Cardinality.Finite.SplitEnumerable.Search using
  ( ∀?
  ; ∃?
  ; module PreInst
  )

import Cardinality.Finite.SplitEnumerable.Search using
  ( ∃?ⁿ
  ; ∃↯ⁿ
  )

import Snippets.Bool using
  ( ∧-comm
  )

-- 4.4: Countdown

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
