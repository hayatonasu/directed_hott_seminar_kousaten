## Agda でノートをとる

Agdaでノートを取りたい人は、このリポジトリを使ってください。
Agdaを使ってない人にも多少読めるものにするために、MarkdownにAgdaのコードを埋め込む方法を使っています。
めんどくさければ、普通にAgdaファイルを使ってください。

## `lagda.md` の使い方

`lagda.md` は、Markdown に Agda のコードを埋め込むための拡張（文芸的プログラミング）です。
` ```agda` と ` ``` ` で囲まれた部分が Agda のコードとして認識されて次のように表示されます。
```agda
{-# OPTIONS --safe --without-K #-}
module example where
open import Agda.Primitive renaming (Set to Type)
```
これはmodule `example` を定義し、`Agda.Primitive` を `Type` にリネームした上でインポートすることを示しています。

例えば、Identity type の定義は次のようになります。
```agda
data _≡_ {A : Type} : A → A → Type where
    refl : ∀ {x} → x ≡ x
```
ここで、`=` はAgdaに既に定義されている等号なので、`≡` という記号を使っています。
Homotopyの定義と $f∼f$ の証明は次のようになります。

```agda
_∼_ : ∀ {A : Type} → {B : A → Type} → (f g : (x : A) → B x) → Type
_∼_ {A} {B} f g = (x : A) → f x ≡ g x

refl-htpy : ∀ {A : Type} {B : A → Type} {f : (x : A) → B x} → f ∼ f
refl-htpy {A} {B} {f} = λ x → refl
```

