---
title: NbE
---

> TODO

```agda
module extra.nbe where
```

## Imports

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
```

## Prelude

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
```

```agda
infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data _⊢_ (Γ : Context) : Type → Set where
  `_  : ∀ {A} → Γ ∋ A → Γ ⊢ A
  ƛ_  : ∀ {A B} → Γ ,- A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
```

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

```agda
Ren : Context → Context → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ren-nf : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊢Nf A → Δ ⊢Nf A

ren-ne : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊢Ne A → Δ ⊢Ne A
ren-ne ρ (` x) = ` ρ x
ren-ne ρ (M · N) = ren-ne ρ M · ren-nf ρ N

ren-nf ρ (ne M) = ne (ren-ne ρ M)
ren-nf ρ (ƛ M) = ƛ ren-nf (λ { Z → Z ; (S x) → S (ρ x) }) M
```

```
infix  4 _⊨_

_⊨_ : Context → Type → Set
Γ ⊨ `ℕ      = Γ ⊢Nf `ℕ
Γ ⊨ (A ⇒ B) = Γ ⊢Ne (A ⇒ B) ⊎ (∀ {Δ} → Ren Γ Δ → Δ ⊨ A → Δ ⊨ B)

reflect : ∀ {Γ A} → Γ ⊢Ne A → Γ ⊨ A
reflect {A = `ℕ}    M = ne M
reflect {A = A ⇒ B} M = inj₁ M

relify : ∀ {Γ A} → Γ ⊨ A → Γ ⊢Nf A
relify {A = `ℕ}    x        = x
relify {A = A ⇒ B} (inj₁ x) = ne x
relify {A = A ⇒ B} (inj₂ y) = ƛ relify (y S (reflect (` Z)))

ren⊨ : ∀ {Γ Δ A} → Ren Γ Δ → Γ ⊨ A → Δ ⊨ A
ren⊨ {A = `ℕ} ρ tp = ren-nf ρ tp
ren⊨ {A = A ⇒ B} ρ (inj₁ x) = inj₁ (ren-ne ρ x)
ren⊨ {A = A ⇒ B} ρ (inj₂ y) = inj₂ (λ ρ' → y (λ x → ρ' (ρ x)))

Env : Context → Context → Set
Env Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊨ A

eval : ∀ {Γ Δ A} → Γ ⊢ A → Env Γ Δ → Δ ⊨ A
eval (` x) η = η x
eval (ƛ M) η = inj₂ λ ρ tp → eval M λ { Z → tp ; (S x) → ren⊨ ρ (η x) }
eval (M · N) η with eval M η
... | inj₁ x = reflect (x · relify (eval N η))
... | inj₂ y = y (λ z → z) (eval N η)

nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢Nf A
nf M = relify (eval M λ x → reflect (` x))
```
