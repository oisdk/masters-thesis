\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Properties where

open import Prelude hiding (B; C)
open import Cubical.Data.Sigma using (Σ≡Prop) public
open import Cubical.Foundations.HLevels using (isOfHLevelΣ) public

private
  variable
    B : A → Type b
    C : Σ A B → Type c
\end{code}
%<*reassoc>
\begin{code}
reassoc : Σ (Σ A B) C ⇔ Σ[ x ⦂ A ] Σ[ y ⦂ B x ] C (x , y)
\end{code}
%</reassoc>
\begin{code}
reassoc .fun       ((x , y) , z)    = x , (y , z)
reassoc .inv       (x , (y , z))    = (x , y) , z
reassoc .leftInv   ((x , y) , z) i  = ((x , y) , z)
reassoc .rightInv  (x , (y , z)) i  = (x , (y , z))

≃Σ≡Prop : ∀ {A : Type a} {u} {U : A → Type u} → ((x : A) → isProp (U x)) → {p q : Σ A U} → (p ≡ q) ≃ (fst p ≡ fst q)
≃Σ≡Prop {A = A} {U = U} pA {p} {q} = isoToEquiv (iso to fro (λ _ → refl) (J Jt Jp))
  where
  to : {p q : Σ A U} → p ≡ q → fst p ≡ fst q
  to = cong fst

  fro : ∀ {p q} → fst p ≡ fst q → p ≡ q
  fro = Σ≡Prop pA

  Jt : (q : Σ A U) → p ≡ q → Type _
  Jt q q≡ = fro (to q≡) ≡ q≡

  Jp : Jt p refl
  Jp i j .fst = p .fst
  Jp i j .snd = isProp→isSet (pA (p .fst)) (p .snd) (p .snd) (λ k → fro {p} {p} (to (refl {x = p})) k .snd) refl i j
\end{code}
