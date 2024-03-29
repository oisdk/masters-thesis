\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.List.Base where

open import Prelude

private
  module DisplayDefinition where
\end{code}
%<*list-def>
\begin{code}
    data List (A : Type a) : Type a where
      []   : List A
      _∷_  : A → List A → List A
\end{code}
%</list-def>
\begin{code}
open import Agda.Builtin.List using (List; _∷_; []) public
open import Data.Fin

foldr : (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

infixr 5 _++_
_++_ : List A → List A → List A
xs ++ ys = foldr _∷_ ys xs

length : List A → ℕ
length = foldr (const suc) zero

infixl 6 _!_
_!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) ! f0 = x
(x ∷ xs) ! fs i = xs ! i

tabulate : ∀ n → (Fin n → A) → List A
tabulate zero f = []
tabulate (suc n) f = f f0 ∷ tabulate n (f ∘ fs)

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = foldr (λ x ys → f x ++ ys) []

map : (A → B) → List A → List B
map f = foldr (λ x xs → f x ∷ xs) []

take : ℕ → List A → List A
take n xs = foldr f (const []) xs n
  where
  f : A → (ℕ → List A) → ℕ → List A
  f x k zero = []
  f x k (suc n) = x ∷ k n
\end{code}
