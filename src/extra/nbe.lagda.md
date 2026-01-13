---
title: NbE
---

> This part is adapted from [System F in Agda, for Fun and Profit](https://doi.org/10.1007/978-3-030-33636-3_10)

```agda
module extra.nbe where
```

## Imports

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
```

## Prelude

We define the intrinsically typed _stlc_ as usual:

```agda
infixr 7 _⇒_

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type

infixl 5 _,-_

data Context : Set where
  ∅    : Context
  _,-_ : Context → Type → Context

infix 4 _∋_

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ ,- A ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → Γ ,- B ∋ A

infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data _⊢_ (Γ : Context) : Type → Set where
  `_  : ∀ {A} → Γ ∋ A → Γ ⊢ A
  ƛ_  : ∀ {A B} → Γ ,- A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
```

Definition of **syntactic** neutral (stuck computation) and normal terms:

```agda
infix  4 _⊢Nf_ _⊢Ne_

data _⊢Nf_ (Γ : Context) : Type → Set

data _⊢Ne_ (Γ : Context) : Type → Set where
  `_  : ∀ {A} → Γ ∋ A → Γ ⊢Ne A
  _·_ : ∀ {A B} → Γ ⊢Ne A ⇒ B → Γ ⊢Nf A → Γ ⊢Ne B

data _⊢Nf_ Γ where
  ne : ∀ {A} → Γ ⊢Ne A → Γ ⊢Nf A 
  ƛ_ : ∀ {A B} → Γ ,- A ⊢Nf B → Γ ⊢Nf A ⇒ B
```

Renaming of neutral and normal terms:

```agda
Ren : Context → Context → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ren-nf : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊢Nf A → Δ ⊢Nf A

ren-ne : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊢Ne A → Δ ⊢Ne A
ren-ne ρ (` x)   = ` ρ x
ren-ne ρ (M · N) = ren-ne ρ M · ren-nf ρ N

ren-nf ρ (ne M) = ne (ren-ne ρ M)
ren-nf ρ (ƛ M)  = ƛ ren-nf (λ { Z → Z ; (S x) → S (ρ x) }) M
```

## Normalization by Evaluation

We define the semantic domain `Γ ⊨ A` as follows, and it looks surprisingly similar
to the semantic types from our _Semantic Typing_ part.

The semantic value is indexed by `Context` and `Type`. 
- For **base type**, since we do not have literals here, it is a (syntactic) normal term.
- For **function type**, it can either be a (syntactic) neutral term or a semantic function, which is a meta (Agda) level function that maps semantic value to another (with an extra argument for renaming).

```agda
infix  4 _⊨_

_⊨_ : Context → Type → Set
Γ ⊨ `ℕ      = Γ ⊢Nf `ℕ
Γ ⊨ (A ⇒ B) = Γ ⊢Ne (A ⇒ B) ⊎ (∀ {Δ} → Ren Γ Δ → Δ ⊨ A → Δ ⊨ B)
```

Reflection lifts a **syntactic** neutral term to semantic term:

```agda
reflect : ∀ {Γ A} → Γ ⊢Ne A → Γ ⊨ A
reflect {A = `ℕ}    M = ne M
reflect {A = A ⇒ B} M = inj₁ M
```

Reification converts the semantic term into **syntactic** (normal) term:

```agda
reify : ∀ {Γ A} → Γ ⊨ A → Γ ⊢Nf A
reify {A = `ℕ}    x        = x
reify {A = A ⇒ B} (inj₁ x) = ne x
reify {A = A ⇒ B} (inj₂ y) = ƛ reify (y S (reflect (` Z)))
```

Renaming of semantic values:

```agda
ren⊨ : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊨ A → Δ ⊨ A
ren⊨ {A = `ℕ}    ρ x        = ren-nf ρ x
ren⊨ {A = A ⇒ B} ρ (inj₁ x) = inj₁ (ren-ne ρ x)
ren⊨ {A = A ⇒ B} ρ (inj₂ y) = inj₂ (λ ρ' → y (λ x → ρ' (ρ x)))
```

An environment is a function that maps a variable to a semantic value 
(under a different context).

```agda
Env : Context → Context → Set
Env Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊨ A
```

Evaluation interprets a **syntactic term** into the semantic term:

```agda
eval : ∀ {Γ Δ A} → Γ ⊢ A → Env Γ Δ → Δ ⊨ A
eval (` x) η = η x
eval (ƛ M) η = inj₂ λ ρ N → eval M λ { Z → N ; (S x) → ren⊨ ρ (η x) }
eval (M · N) η with eval M η
... | inj₁ x = reflect (x · reify (eval N η))
... | inj₂ y = y (λ z → z) (eval N η)
```

Normalization proceeds with evaluation and reification:

```agda
norm : ∀ {Γ A} → Γ ⊢ A → Γ ⊢Nf A
norm M = reify (eval M λ x → reflect (` x))
```
