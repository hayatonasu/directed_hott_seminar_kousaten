
# 1章
```agda
{-# OPTIONS --safe --without-K #-}
module firstsection where
open import Agda.Primitive renaming (Set to Type)
open import example
```


```agda
data  Σ ( A : Type ) (B : A → Type) : Type where
    pair : (a : A) → (b : B a) → Σ A B 

fst : {A : Type} {B : A → Type} → Σ A B → A
fst (pair a b) = a

snd : {A : Type} {B : A → Type} → ( p : Σ A B ) → B (fst p)
snd (pair a b) = b

has-extensional-Σ : (A : Type) (B : A → Type) → Set₁
has-extensional-Σ A B = ∀ (P : Σ A B → Type) →
    ( (x : A) → (y : B x) → P (pair x y) ) → (p : Σ A B) → P p
```