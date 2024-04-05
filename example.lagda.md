
```agda
{-# OPTIONS --safe --without-K #-}
module example where
open import Agda.Primitive renaming (Set to Type)
```

```agda
data _≅_ {A : Type} : A → A → Type where
    refl : ∀ {x} → x ≅ x
    
```

```agda
_∼_ : ∀ {A : Type} → {B : A → Type} → (f g : (x : A) → B x) → Type
_∼_ {A} {B} f g = (x : A) → f x ≅ g x

refl-htpy : ∀ {A : Type} {B : A → Type} {f : (x : A) → B x} → f ∼ f
refl-htpy {A} {B} {f} = {!   !}

```