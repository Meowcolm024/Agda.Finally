---
title: Properties
---

> TODO

we also start with imports

```agda
module stlc.prop where

open import stlc.base

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)

private
  variable
    n m : ℕ
```

renmaing and substitution preserves typing

```agda
ty-rename : ∀ {M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m ρ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B)
    --------------------------------------------------------------
  → Δ ⊢ rename ρ M ⦂ A
ty-rename (⊢var x)       Φ = ⊢var (Φ x)
ty-rename (⊢abs ⊢M)      Φ = ⊢abs (ty-rename ⊢M λ { Z → Z ; (S ∋x) → S (Φ ∋x) })
ty-rename (⊢app ⊢M ⊢N)   Φ = ⊢app (ty-rename ⊢M Φ) (ty-rename ⊢N Φ)
ty-rename ⊢true          Φ = ⊢true
ty-rename ⊢false         Φ = ⊢false
ty-rename (⊢if ⊢L ⊢M ⊢N) Φ = ⊢if (ty-rename ⊢L Φ) (ty-rename ⊢M Φ) (ty-rename ⊢N Φ)

ty-subst : ∀ {M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m σ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ⊢ σ x ⦂ B)
    --------------------------------------------------------------
  → Δ ⊢ subst σ M ⦂ A
ty-subst (⊢var x)       Φ = Φ x
ty-subst (⊢abs ⊢M)      Φ = ⊢abs (ty-subst ⊢M λ { Z → ⊢var Z ; (S ∋x) → ty-rename (Φ ∋x) S })
ty-subst (⊢app ⊢M ⊢N)   Φ = ⊢app (ty-subst ⊢M Φ) (ty-subst ⊢N Φ)
ty-subst ⊢true          Φ = ⊢true
ty-subst ⊢false         Φ = ⊢false
ty-subst (⊢if ⊢L ⊢M ⊢N) Φ = ⊢if (ty-subst ⊢L Φ) (ty-subst ⊢M Φ) (ty-subst ⊢N Φ)
```
