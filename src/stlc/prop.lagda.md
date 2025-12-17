---
title: Properties
---

> WIP

```agda
module stlc.prop where
```

## Imports

```agda
open import stlc.base

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
```

## Some Useful Lemmas

renaming preserves typing

```agda
ty-ext : ∀ {n A} {Γ : Context n}
  → ∀ {m ρ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B)
    --------------------------------------------------------------
  → ∀ {x B} → Γ ,- A ∋ x ⦂ B → Δ ,- A ∋ ext ρ x ⦂ B
ty-ext ⊢ρ Z     = Z
ty-ext ⊢ρ (S x) = S (⊢ρ x)

ty-rename : ∀ {n M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m ρ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B)
    --------------------------------------------------------------
  → Δ ⊢ rename ρ M ⦂ A
ty-rename (⊢var x)       ⊢ρ = ⊢var (⊢ρ x)
ty-rename (⊢abs ⊢M)      ⊢ρ = ⊢abs (ty-rename ⊢M (ty-ext ⊢ρ))
ty-rename (⊢app ⊢M ⊢N)   ⊢ρ = ⊢app (ty-rename ⊢M ⊢ρ) (ty-rename ⊢N ⊢ρ)
ty-rename ⊢true          ⊢ρ = ⊢true
ty-rename ⊢false         ⊢ρ = ⊢false
ty-rename (⊢if ⊢L ⊢M ⊢N) ⊢ρ = ⊢if (ty-rename ⊢L ⊢ρ) (ty-rename ⊢M ⊢ρ) (ty-rename ⊢N ⊢ρ)
```

and substitution preserves typing

```agda
ty-exts : ∀ {n A} {Γ : Context n}
  → ∀ {m σ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ⊢ σ x ⦂ B)
    --------------------------------------------------------------
  → ∀ {x B } → Γ ,- A ∋ x ⦂ B → Δ ,- A ⊢ exts σ x ⦂ B
ty-exts ⊢σ Z     = ⊢var Z
ty-exts ⊢σ (S x) = ty-rename (⊢σ x) S

ty-subst : ∀ {n M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m σ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ⊢ σ x ⦂ B)
    --------------------------------------------------------------
  → Δ ⊢ subst σ M ⦂ A
ty-subst (⊢var x)       ⊢σ = ⊢σ x
ty-subst (⊢abs ⊢M)      ⊢σ = ⊢abs (ty-subst ⊢M (ty-exts ⊢σ))
ty-subst (⊢app ⊢M ⊢N)   ⊢σ = ⊢app (ty-subst ⊢M ⊢σ) (ty-subst ⊢N ⊢σ)
ty-subst ⊢true          ⊢σ = ⊢true
ty-subst ⊢false         ⊢σ = ⊢false
ty-subst (⊢if ⊢L ⊢M ⊢N) ⊢σ = ⊢if (ty-subst ⊢L ⊢σ) (ty-subst ⊢M ⊢σ) (ty-subst ⊢N ⊢σ)
```

## Progress and Preservation

preservation

```agda
preservation : ∀ {M M' A}
  → ∅ ⊢ M ⦂ A
  → M —→ M'
    -----------
  → ∅ ⊢ M' ⦂ A
preservation (⊢app ⊢M ⊢N)        (ξ-app₁ M→M') = ⊢app (preservation ⊢M M→M') ⊢N
preservation (⊢app ⊢M ⊢N)        (ξ-app₂ N→N') = ⊢app ⊢M (preservation ⊢N N→N')
preservation (⊢app (⊢abs ⊢M) ⊢N) (β-abs VN)    = ty-subst ⊢M λ { Z → ⊢N }
preservation (⊢if ⊢L ⊢M ⊢N)      (ξ-if L→L')   = ⊢if (preservation ⊢L L→L') ⊢M ⊢N
preservation (⊢if ⊢L ⊢M ⊢N)      β-if₁         = ⊢M
preservation (⊢if ⊢L ⊢M ⊢N)      β-if₂         = ⊢N
```

progress

```agda
data Progress {n} : Term n → Set where

  step : ∀ {M N : Term n}
    → M —→ N
      -----------
    → Progress M

  done : ∀ {M : Term n}
    → Value M
      -----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → Progress M
progress (⊢abs ⊢M)                       = done V-abs
progress (⊢app ⊢M ⊢N) with progress ⊢M
... | step M—→M'                         = step (ξ-app₁ M—→M')
... | done V-abs with progress ⊢N
...   | step N—→N'                       = step (ξ-app₂ N—→N')
...   | done VN                          = step (β-abs VN)
progress ⊢true                           = done V-true
progress ⊢false                          = done V-false
progress (⊢if ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L'                         = step (ξ-if L—→L')
... | done V-true                        = step β-if₁
... | done V-false                       = step β-if₂
```