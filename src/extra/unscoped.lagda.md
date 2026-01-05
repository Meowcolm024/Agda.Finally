---
title: Unscoped
---

> The part follows [Autosubst: Automation for de Bruijn syntax and substitution in Coq](https://www.ps.uni-saarland.de/autosubst/)

```agda
module extra.unscoped where
```

We consider the stlc with unscoped debruijn index (using parallel substitution) here.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_∘_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
```

## Axioms

```agda
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

Functional extensionality.

## Basics

Definition of types:

```agda
infixr 7 _⇒_

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type
```

Context is just a function from `Nat` to `Type`:

```agda
Context : Set
Context = ℕ → Type
```

Context extension (We define a general version here so we can use it as extension of substitution).

```
infix  6 _•_

_•_ : ∀ {A : Set} → A → (ℕ → A) → (ℕ → A)
(A • σ) zero    = A
(A • σ) (suc x) = σ x
```

Definition of terms:

```agda
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data Term : Set where
  `_  : ℕ → Term
  ƛ_  : Term → Term
  _·_ : Term → Term → Term
```

Typing is standard:

```agda
infix  4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢var : ∀ {Γ x A}
    → Γ x ≡ A
      ------------
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {Γ A B M}
    → A • Γ ⊢ M ⦂ B
      ----------------
    → Γ ⊢ ƛ M ⦂ A ⇒ B

  ⊢app : ∀ {Γ A B M N}
    → Γ ⊢ M ⦂ A ⇒ B
    → Γ ⊢ N ⦂ A
      --------------
    → Γ ⊢ M · N ⦂ B
```

## Renaming and Substitution

Renaming and substitution are basically identical to our well scoped version:

```agda
ids : ℕ → Term
ids x = ` x

ext : (ℕ → ℕ) → (ℕ → ℕ)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : (ℕ → ℕ) → Term → Term
rename ρ (` x)   = ` ρ x
rename ρ (ƛ M)   = ƛ (rename (ext ρ) M)
rename ρ (M · N) = (rename ρ M) · (rename ρ N)

exts : (ℕ → Term) → (ℕ → Term)
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

subst : (ℕ → Term) → Term → Term
subst σ (` x)   = σ x
subst σ (ƛ M)   = ƛ (subst (exts σ) M)
subst σ (M · N) = (subst σ M) · (subst σ N)

_[_] : Term → Term → Term
M [ N ] = subst (N • ids) M
```

Definition of values and reduction:

```agda
data Value : Term → Set where
  V-abs : ∀ {M} → Value (ƛ M)

infix  4 _—→_

data _—→_ : Term → Term → Set where
  ξ-app₁ : ∀ {M M' N}
    → M —→ M'
      -----------------
    → M · N —→ M' · N

  ξ-app₂ : ∀ {M N N'}
    → N —→ N'
      ------------------------
    → (ƛ M) · N —→ (ƛ M) · N'

  β-abs : ∀ {M N}
    → Value N
      ---------------------
    → (ƛ M) · N —→ M [ N ]
```

## Properties

Before showing renaming and substitution preserves typing, 
we need a few lemmas between renaming, extension and substitution:

```agda

ren : (ℕ → ℕ) → (ℕ → Term)
ren ρ = ids ∘ ρ

ren-ext : ∀ {ρ} → ren (ext ρ) ≡ exts (ren ρ)
ren-ext {ρ} = extensionality λ { zero → refl ; (suc x) → refl }

rename-subst-ren : ∀ {ρ M} → rename ρ M ≡ subst (ren ρ) M
rename-subst-ren {ρ} {` x}   = refl
rename-subst-ren {ρ} {ƛ M}   rewrite rename-subst-ren {ext ρ} {M} | ren-ext {ρ} = refl
rename-subst-ren {ρ} {M · N} rewrite rename-subst-ren {ρ} {M} | rename-subst-ren {ρ} {N} = refl
```

Renaming preserves typing:

```agda
ty-ext : ∀ {Γ} {A : Type}
  → ∀ {ρ Δ} → (∀ x → Γ x ≡ Δ (ρ x))
    --------------------------------------
  → (∀ x → (A • Γ) x ≡ (A • Δ) (ext ρ x))
ty-ext ⊢ρ zero    = refl
ty-ext ⊢ρ (suc x) =  ⊢ρ x

ty-ren : ∀ {Γ M A}
  → Γ ⊢ M ⦂ A
  → ∀ {ρ Δ} → (∀ x → Γ x ≡ Δ (ρ x))
    --------------------------------
  → Δ ⊢ subst (ren ρ) M ⦂ A
ty-ren (⊢var {x = x} refl) ⊢ρ = ⊢var (Eq.sym (⊢ρ x))
ty-ren (⊢abs ⊢M) {ρ}       ⊢ρ rewrite Eq.sym (ren-ext {ρ}) = ⊢abs (ty-ren ⊢M (ty-ext ⊢ρ))
ty-ren (⊢app ⊢M ⊢N)        ⊢ρ = ⊢app (ty-ren ⊢M ⊢ρ) (ty-ren ⊢N ⊢ρ)
```

Substitution preserves typing:

```agda

ty-exts : ∀ {Γ A}
  → ∀ {σ Δ} → (∀ x → Δ ⊢ σ x ⦂ Γ x)
    -------------------------------------
  → (∀ x → A • Δ ⊢ exts σ x ⦂ (A • Γ) x)
ty-exts {σ = σ} ⊢σ zero    = ⊢var refl
ty-exts {σ = σ} ⊢σ (suc x) rewrite rename-subst-ren {suc} {σ x} = ty-ren (⊢σ x) (λ _ → refl)

ty-subst : ∀ {Γ M A}
  → Γ ⊢ M ⦂ A
  → ∀ {σ Δ} → (∀ x → Δ ⊢ σ x ⦂ Γ x)
    --------------------------------
  → Δ ⊢ subst σ M ⦂ A
ty-subst (⊢var {x = x} refl) ⊢σ = ⊢σ x
ty-subst (⊢abs ⊢M) {σ}       ⊢σ = ⊢abs (ty-subst ⊢M {exts σ} (ty-exts ⊢σ))
ty-subst (⊢app ⊢M ⊢N)        ⊢σ = ⊢app (ty-subst ⊢M ⊢σ) (ty-subst ⊢N ⊢σ)
```

Preservation is straightforward:

```agda
ty-pres : ∀ {Γ M M' A}
  → Γ ⊢ M ⦂ A → M —→ M'
    --------------------
  → Γ ⊢ M' ⦂ A
ty-pres (⊢app ⊢M ⊢N)        (ξ-app₁ M→M') = ⊢app (ty-pres ⊢M M→M') ⊢N
ty-pres (⊢app ⊢M ⊢N)        (ξ-app₂ M→M') = ⊢app ⊢M (ty-pres ⊢N M→M')
ty-pres (⊢app (⊢abs ⊢M) ⊢N) (β-abs VN)    = ty-subst ⊢M λ { zero → ⊢N ; (suc x) → ⊢var refl }
```

Progress is a bit more complicated, as we need to first define the predicate for *empty context*:

```agda
Closed : Context → Set
Closed Γ = ∀ {x A} → ¬ (Γ x ≡ A)
```

And now we can proceed with progress:

```agda
ty-prog : ∀ {Γ M A}
  → Closed Γ → Γ ⊢ M ⦂ A
    --------------------------
  → ∃[ M' ] M —→ M' ⊎ Value M
ty-prog ∅ (⊢var x)                               = ⊥-elim (∅ x)
ty-prog ∅ (⊢abs ⊢M)                              = inj₂ V-abs
ty-prog ∅ (⊢app {N = N} ⊢M ⊢N) with ty-prog ∅ ⊢M
... | inj₁ (M' , M→M')                           = inj₁ (M' · N , ξ-app₁ M→M')
... | inj₂ (V-abs {M = M}) with ty-prog ∅ ⊢N
...   | inj₁ (N' , N→N')                         = inj₁ ((ƛ M) · N' , ξ-app₂ N→N')
...   | inj₂ (V-abs {M = N})                     = inj₁ ((M [ ƛ N ]) , β-abs V-abs)
```