module Data.Permutation where

open import Prelude
open import Data.Fin
open import Data.Nat

Perm : ℕ → Type₀
Perm zero    = ⊤
Perm (suc n) = Fin (suc n) × Perm n

private variable n m : ℕ

shift : Fin (suc n) → Fin n → Fin (suc n)
shift f0 = fs
shift {n = suc _} (fs i) f0     = f0
shift {n = suc _} (fs i) (fs j) = fs (shift i j)

index : Perm n → Fin n → Fin n
index {n = suc n} (x , xs) f0 = x
index {n = suc n} (x , xs) (fs i) = shift x (index xs i)

_≡ᶠᵇ_ : Fin n → Fin n → Bool
_≡ᶠᵇ_ {n = suc n} f0 f0 = true
_≡ᶠᵇ_ {n = suc n} f0 (fs x) = false
_≡ᶠᵇ_ {n = suc n} (fs x) f0 = false
_≡ᶠᵇ_ {n = suc n} (fs x) (fs y) = x ≡ᶠᵇ y

_≢ᶠ_ : Fin n → Fin n → Type
x ≢ᶠ y = T (not (x ≡ᶠᵇ y))

isPropT : {b : Bool} → isProp (T b)
isPropT {b = false} = isProp⊥
isPropT {b = true} _ _ = refl

pull : (x y : Fin (suc n)) → x ≢ᶠ y → Fin n
pull f0                 (fs y) _ = y
pull {n = suc _} (fs x) f0     _ = f0
pull {n = suc _} (fs x) (fs y) p = fs (pull x y p)

shift∘pull : ∀ (x y : Fin (suc n)) → (p : x ≢ᶠ y) → shift x (pull x y p) ≡ y
shift∘pull f0 (fs x) _ = refl
shift∘pull {n = suc _} (fs x) f0 _ = refl
shift∘pull {n = suc _} (fs x) (fs y) p = cong fs (shift∘pull x y p)

pull≢shift : ∀ (x : Fin (suc n)) y → x ≢ᶠ shift x y
pull≢shift f0 y = tt
pull≢shift {n = suc _} (fs x) f0 = tt
pull≢shift {n = suc _} (fs x) (fs y) = pull≢shift x y

pull∘shift : ∀ (x : Fin (suc n)) y → pull x (shift x y) (pull≢shift x y) ≡ y
pull∘shift f0 y = refl
pull∘shift {n = suc _} (fs x) f0 = refl
pull∘shift {n = suc _} (fs x) (fs y) = cong fs (pull∘shift x y)

FInjection : (Fin n → Fin m) → Type
FInjection f = ∀ x y → x ≢ᶠ y → f x ≢ᶠ f y

_F↣_ : ℕ → ℕ → Type
n F↣ m = Σ[ f ⦂ (Fin n → Fin m) ] FInjection f

pull-inj : (x y z : Fin (suc n)) → (p : x ≢ᶠ y) → (q : x ≢ᶠ z) → y ≢ᶠ z → pull x y p ≢ᶠ pull x z q
pull-inj f0 (fs y) (fs z) _ _ p = p
pull-inj {n = suc _} (fs _) f0 (fs _) _ _ _ = tt
pull-inj {n = suc _} (fs _) (fs _) f0 _ _ _ = tt
pull-inj {n = suc _} (fs x) (fs y) (fs z) p q r = pull-inj x y z p q r

pull′ : suc n F↣ suc n → n F↣ n
pull′ f .fst i = pull (f .fst f0) (f .fst (fs i)) (f .snd _ _ tt)
pull′ f .snd x y x≢y = pull-inj (f .fst f0) (f .fst (fs x)) (f .fst (fs y)) (f .snd _ _ tt) (f .snd _ _ tt) (f .snd _ _ x≢y)

tabulate : (n F↣ n) → Perm n
tabulate {zero}  _ = tt
tabulate {suc n} f = f .fst f0 , tabulate (pull′ f)

open import Path.Reasoning

index∘tabulate : ∀ n (f : n F↣ n) i → index (tabulate f) i ≡ f .fst i
index∘tabulate (suc n) f f0     = refl
index∘tabulate (suc n) f (fs i) =
  shift (f .fst f0) (index (tabulate (pull′ f)) i) ≡⟨ cong (shift (f .fst f0)) (index∘tabulate n _ _) ⟩
  shift (f .fst f0) (pull (f .fst f0) (f .fst (fs i)) (f .snd  _ _ tt)) ≡⟨ shift∘pull (f .fst f0) (f .fst (fs i)) (f .snd _ _ tt) ⟩
  f .fst (fs i) ∎

shift-inj : ∀ (x : Fin (suc n)) y z → y ≢ᶠ z → shift x y ≢ᶠ shift x z
shift-inj f0 y z p = p
shift-inj {n = suc _} (fs x) f0 (fs x₁) p = tt
shift-inj {n = suc _} (fs x) (fs x₁) f0 p = tt
shift-inj {n = suc _} (fs x) (fs y) (fs z) p = shift-inj x y z p

≢ᶠ-sym : (x y : Fin n) → x ≢ᶠ y → y ≢ᶠ x
≢ᶠ-sym {n = suc _} f0 (fs x) p = tt
≢ᶠ-sym {n = suc _} (fs x) f0 p = tt
≢ᶠ-sym {n = suc _} (fs x) (fs y) p = ≢ᶠ-sym x y p

index-inj : (xs : Perm n) → FInjection (index xs)
index-inj {n = zero} tt () y p
index-inj {n = suc n} xs f0 (fs x) p = pull≢shift (xs .fst) _
index-inj {n = suc n} xs (fs x) f0 p = ≢ᶠ-sym (xs .fst) (shift (xs .fst) (index (xs .snd) x)) (pull≢shift (xs .fst) _)
index-inj {n = suc n} (x , xs) (fs i) (fs j) p = shift-inj x _ _ (index-inj xs i j p)

open import Cubical.Foundations.Everything using (isPropΠ; isProp→)

isProp-inj : (f : Fin n → Fin n) → isProp (FInjection f)
isProp-inj f = isPropΠ λ _ → isPropΠ λ _ → isProp→ isPropT

tabulate∘index : ∀ n (xs : Perm n) → tabulate (index xs , index-inj xs) ≡ xs
tabulate∘index zero    xs       = refl
tabulate∘index (suc n) (x , xs) = 
  tabulate (index (x , xs) , index-inj (x , xs)) ≡⟨ cong (x ,_) (cong tabulate (Σ≡Prop isProp-inj  (funExt λ i → pull∘shift x (index xs i)))) ⟩
  (x , tabulate (index xs , index-inj xs)) ≡⟨ cong (x ,_) (tabulate∘index n xs) ⟩
  (x , xs) ∎

T? : (b : Bool) → Dec (T b)
T? false = no (λ z → z)
T? true = yes tt

find : Perm n → Fin n → Fin n
find {n = suc _} (x , xs) y with T? (not (x ≡ᶠᵇ y))
... | no  x≡y = f0
... | yes x≢y = fs (find xs (pull x y x≢y))

¬x≢x : (x : Fin n) → ¬ (x ≢ᶠ x)
¬x≢x {n = suc _} (fs x) p = ¬x≢x x p

find∘ind : ∀ (xs : Perm n) i → find xs (index xs i) ≡ i
find∘ind {n = suc _} (x , xs) f0 with T? (not (x ≡ᶠᵇ x))
... | yes x≢x = ⊥-elim (¬x≢x x x≢x)
... | no  res = refl
find∘ind {n = suc _} (x , xs) (fs y) with T? (not (x ≡ᶠᵇ shift x (index xs y)))
... | no  x≡ = ⊥-elim (x≡ (pull≢shift  x (index xs y)))
... | yes x≢ = cong fs (cong (find xs) (cong (pull x _) (isPropT _ _) ; pull∘shift x (index xs y)) ; find∘ind xs y)

¬x≢y→x≡y : (x y : Fin n) → ¬ x ≢ᶠ y → x ≡ y
¬x≢y→x≡y {n = suc _} f0 f0 p = refl
¬x≢y→x≡y {n = suc _} f0 (fs x) p = ⊥-elim (p tt)
¬x≢y→x≡y {n = suc _} (fs x) f0 p = ⊥-elim (p tt)
¬x≢y→x≡y {n = suc _} (fs x) (fs y) p = cong fs (¬x≢y→x≡y x y p)

ind∘find : ∀ (p : Perm n) i → index p (find p i) ≡ i
ind∘find {n = suc _} (p , ps) i with T? (not (p ≡ᶠᵇ i))
... | yes p≢i = cong (shift p) (ind∘find ps _) ; shift∘pull p i p≢i
... | no  p≡i = ¬x≢y→x≡y p i p≡i

≢→≢ᶠ : (x y : Fin n) → x ≢ y → x ≢ᶠ y
≢→≢ᶠ {n = suc _} f0 f0 p = ⊥-elim (p refl)
≢→≢ᶠ {n = suc _} f0 (fs x) p = tt
≢→≢ᶠ {n = suc _} (fs x) f0 p = tt
≢→≢ᶠ {n = suc _} (fs x) (fs y) p = ≢→≢ᶠ x y (p ∘ cong fs)

open import Data.Fin.Properties using (pred; isSetFin)
open import Data.Maybe.Properties using (just≢nothing; nothing≢just)

≡→≡ᶠ :  (x y : Fin n) → x ≡ y → ¬ (x ≢ᶠ y)
≡→≡ᶠ {n = suc _} f0 (fs x) p q = nothing≢just p
≡→≡ᶠ {n = suc _} (fs x) f0 p q = just≢nothing p
≡→≡ᶠ {n = suc (suc _)} (fs x) (fs y) p q = ≡→≡ᶠ x y (cong pred p) q

⇔→F↣ : (i : Fin n ⇔ Fin n) → FInjection (i .fun)
⇔→F↣ i x y p = ≢→≢ᶠ (i .fun x) (i .fun y)
  λ fx≡fy → ≡→≡ᶠ x y (sym (i .leftInv x) ; cong (i .inv) fx≡fy ; i .leftInv y) p

Perm⇔ : ∀ n → Perm n ⇔ (Fin n ⇔ Fin n)
Perm⇔ n .fun p .fun = index p
Perm⇔ n .fun p .inv = find p
Perm⇔ n .fun p .rightInv = ind∘find p
Perm⇔ n .fun p .leftInv = find∘ind p
Perm⇔ n .inv i = tabulate (i .fun , ⇔→F↣ i)
Perm⇔ n .rightInv i = iso-fun-inj isSetFin _ _ (funExt (index∘tabulate n (i .fun , ⇔→F↣ i)))
Perm⇔ n .leftInv  p = cong tabulate (Σ≡Prop isProp-inj refl) ; tabulate∘index n p
