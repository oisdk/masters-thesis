\begin{code}
{-# OPTIONS --cubical --safe #-}

module Dyck where

open import Prelude hiding (_⟨_⟩_)
open import Data.List
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Data.Fin
open import Data.List.Membership
import Data.Nat as ℕ
open import Agda.Builtin.Nat using (_-_; _+_)
open import Data.Nat.Properties using (pred)
open import Data.Vec.Iterated

private
  variable
    n m k : ℕ
infixr 6 ⟨_ ⟩_
\end{code}
%<*dyck-def>
\begin{code}
data Dyck : ℕ → ℕ → Type₀ where
  done : Dyck zero zero
  ⟨_ : Dyck (suc n) m → Dyck n (suc m)
  ⟩_ : Dyck n m → Dyck (suc n) m
\end{code}
%</dyck-def>
\begin{code}
private
  module DyckExamples where
\end{code}
%<*dyck-0-2>
\begin{code}
    _ : Dyck 0 2
    _ = ⟨ ⟩ ⟨ ⟩ done
\end{code}
%</dyck-0-2>
%<*dyck-0-3>
\begin{code}
    _ : Dyck 0 3
    _ = ⟨ ⟩ ⟨ ⟨ ⟩ ⟩ done
\end{code}
%</dyck-0-3>
%<*dyck-1-2>
\begin{code}
    _ : Dyck 1 2
    _ = ⟩ ⟨ ⟩ ⟨ ⟩ done
\end{code}
%</dyck-1-2>
\begin{code}
support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  Diff : Type₀ → Type₁
  Diff A = ∀ {B : Type₀} → (A → B) → List B → List B

  mutual
    sup-k : ∀ n m → Diff (Dyck n m)
    sup-k n m k = end n m k ∘ lefts n m k ∘ rights n m k

    lefts : ∀ n m → Diff (Dyck n m)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : ∀ n m → Diff (Dyck n m)
    rights (suc n) m k = sup-k n m (k ∘ ⟩_)
    rights zero    m k = id

    end : ∀ n m → Diff (Dyck n m)
    end (suc _) _    k = id
    end zero (suc _) k = id
    end zero zero    k xs = k done ∷ xs

cover-dyck : (x : Dyck n m) → x ∈ support-dyck n m
cover-dyck x = go _ _ x id []
  where
  open ListDyck

  mutual
    pushLefts : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ lefts n m k xs
    pushLefts n (suc m) k = pushSup (suc n) m (λ z → k (⟨ z))
    pushLefts _ zero    k x xs p = p

    pushEnd : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ end n m k xs
    pushEnd (suc _) _ k x xs p = p
    pushEnd zero (suc _) k x xs p = p
    pushEnd zero zero k x xs (i , p) = fs i , p

    pushRights : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ rights n m k xs
    pushRights (suc n) m k = pushSup n m (λ z → k (⟩ z))
    pushRights zero _ k x xs p = p

    pushSup : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ sup-k n m k xs
    pushSup n m k x xs p = pushEnd n m k x (lefts n m k (rights n m k xs)) (pushLefts n m k x (rights n m k xs) (pushRights n m k x xs p))

  go : ∀ n m → (x : Dyck n m) → (k : Dyck n m → A) → (xs : List A) → k x ∈ sup-k n m k xs
  go zero zero done k xs = f0 , refl
  go zero    (suc m) (⟨ x) k xs = go (suc zero) m x (k ∘ ⟨_) (rights (zero) (suc m) k xs)
  go (suc n) (suc m) (⟨ x) k xs = go (suc (suc n)) m x (k ∘ ⟨_) (rights (suc n) (suc m) k xs)
  go (suc n) m (⟩ x) k xs =
    let p = go n m x (k ∘ ⟩_) xs
    in pushEnd (suc n) m k (k (⟩ x)) (lefts (suc n) m k _) (pushLefts (suc n) m k (k (⟩ x)) (rights (suc n) m k xs) p)

ℰ!⟨Dyck⟩ : ℰ! (Dyck n m)
ℰ!⟨Dyck⟩ .fst = support-dyck _ _
ℰ!⟨Dyck⟩ .snd = cover-dyck

private
  module NonParamTree where
\end{code}
%<*tree-simpl-def>
\begin{code}
    data Tree : Type₀ where
      leaf : Tree
      _*_ : Tree → Tree → Tree
\end{code}
%</tree-simpl-def>
%<*from-dyck>
\begin{code}
    dyck→tree : Dyck zero n → Tree
    dyck→tree d = go d (leaf , _)
      where
      go : Dyck n m → Vec Tree (suc n) → Tree
      go (⟨ d)  ts              = go d (leaf , ts)
      go (⟩ d)  (t₁ , t₂ , ts)  = go d (t₂ * t₁ , ts)
      go done   (t , _)         = t
\end{code}
%</from-dyck>
\begin{code}
data Tree (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  leaf : B → Tree A B
  _⟨_⟩_ : Tree A B → A → Tree A B → Tree A B

fromDyck : Dyck 0 n → Vec A n → Vec B (suc n) → Tree A B
fromDyck xs ops (val , vals) = go xs (leaf val) _ vals ops _
  where
  go : Dyck n m → Tree A B → Vec (Tree A B) n → Vec B m → Vec A m → Vec A n → Tree A B
  go done   t _       vls        ops₁ ops₂ = t
  go (⟩ xs) x (y , s) vls        ops₁ (op , ops₂) = go xs (y ⟨ op ⟩ x) s vls ops₁ ops₂
  go (⟨ xs) t s       (vl , vls) (op , ops₁) ops₂ = go xs (leaf vl) (t , s) vls ops₁ (op , ops₂)
\end{code}
