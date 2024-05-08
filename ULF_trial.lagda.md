```agda
{-# OPTIONS --prop #-}
module ULF_trial where
open import Agda.Primitive


data ⊥ : 
    Prop where

record ⊤ : Prop where
    constructor tt

postulate
    □ : {A : Set} → Set
    * : {A : Set} → Set
    □→⋆ : {A : Set} → □ {A} → * {A}

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

data Nat : Set where
    zero : Nat
    suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}




□Set : Set₁
□Set = Σ Set (λ A → □ {A})

*Set : Set₁
*Set = Σ Set (λ A → * {A})

□→⋆Set : □Set → *Set
□→⋆Set (A , p) = A , ( □→⋆ {A} p)


```