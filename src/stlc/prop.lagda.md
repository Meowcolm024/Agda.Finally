---
title: Properties
---

```agda
module stlc.prop where
```

We show a few basic lemmas related to typing and reduction here.

## Imports

```agda
open import stlc.base
open multistep

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
```

## Some Useful Lemmas

Before we can prove progress and preservation, we need to first show that renaming and
substitution preserves typing.

The lemma `ty-rename` basically states that: given a term `M` with type `A` under context `Γ`,
and a renaming function `ρ` that maps all variables from context `Γ` to `Δ` while preserving their types,
the renamed term is still typed `A` under the new context `Δ`.

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

Similarly, for substitution:

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

## Main Lemmas

**Preservation**: small step reduction (of a *closed* term) preserves typing.
It proceeds by induction on the typing judgement and the reduction.

Note that we need to use the lemma `ty-subst` for the beta rules `β-abs` to show
that typing is preserved in single substitution.

```agda
preservation : ∀ {M M' A}
  → ∅ ⊢ M ⦂ A
  → M —→ M'
    -----------
  → ∅ ⊢ M' ⦂ A
preservation (⊢app ⊢M ⊢N)        (ξ-app₁ M→M') = ⊢app (preservation ⊢M M→M') ⊢N
preservation (⊢app ⊢M ⊢N)        (ξ-app₂ N→N') = ⊢app ⊢M (preservation ⊢N N→N')
preservation (⊢app (⊢abs ⊢M) ⊢N) (β-abs VN)    = ty-subst ⊢M (λ { Z → ⊢N })
preservation (⊢if ⊢L ⊢M ⊢N)      (ξ-if L→L')   = ⊢if (preservation ⊢L L→L') ⊢M ⊢N
preservation (⊢if ⊢L ⊢M ⊢N)      β-if₁         = ⊢M
preservation (⊢if ⊢L ⊢M ⊢N)      β-if₂         = ⊢N
```

**Progress**: a well typed term can either take a step or it is a value.
It proceeds on the induction of the typing judgement.

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

A value of type `Bool` is either `true` or `false`.

```agda
Canonical-Bool : ∀ {n M} {Γ : Context n}
  → Γ ⊢ M ⦂ Bool
  → Value M
    ---------------------
  → M ≡ true ⊎ M ≡ false
Canonical-Bool ⊢true  V-true  = inj₁ refl
Canonical-Bool ⊢false V-false = inj₂ refl
```

A value of the function type is a lambda abstraction.

```agda
Canonical-⇒ : ∀ {n M A B} {Γ : Context n}
  → Γ ⊢ M ⦂ A ⇒ B
  → Value M
    ---------------
  → ∃[ N ] M ≡ ƛ N
Canonical-⇒ {M = ƛ N} (⊢abs ⊢N) V-abs = N , refl
```

Value does not step.

```agda
V-¬—→ : ∀ {n} {M N : Term n}
  → Value M
    -----------
  → ¬ (M —→ N)
V-¬—→ V-abs   ()
V-¬—→ V-true  ()
V-¬—→ V-false ()
```

Small step reduction is deterministic.

```agda
—→-determ : ∀ {n} {M N N' : Term n}
  → M —→ N → M —→ N'
    -----------------
  → N ≡ N'
—→-determ (ξ-app₁ M→N) (ξ-app₁ M→N') rewrite —→-determ M→N M→N' = refl
—→-determ (ξ-app₁ M→N) (ξ-app₂ M→N') = ⊥-elim (V-¬—→ V-abs M→N)
—→-determ (ξ-app₂ M→N) (ξ-app₁ M→N') = ⊥-elim (V-¬—→ V-abs M→N')
—→-determ (ξ-app₂ M→N) (ξ-app₂ M→N') rewrite —→-determ M→N M→N' = refl
—→-determ (ξ-app₂ M→N) (β-abs V')    = ⊥-elim (V-¬—→ V' M→N)
—→-determ (β-abs V)    (ξ-app₂ M→N') = ⊥-elim (V-¬—→ V M→N')
—→-determ (β-abs V)    (β-abs V')    = refl
—→-determ (ξ-if M→N)   (ξ-if M→N')   rewrite —→-determ M→N M→N' = refl
—→-determ β-if₁        β-if₁         = refl
—→-determ β-if₂        β-if₂         = refl
```

## Lemmas for Multi-step

Multi-step is transitive.

```agda
—→*-trans : ∀ {n} {L M N : Term n}
  → L —→* M → M —→* N
    ------------------
  → L —→* N
—→*-trans (L ∎)                  M—→*N = M—→*N
—→*-trans (L —→⟨ L—→L' ⟩ L'—→*M) M—→*N = step—→ L (—→*-trans L'—→*M M—→*N) L—→L'
```

Multi-step preserves typing.

```agda
—→*-pres : ∀ {A M M'} → ∅ ⊢ M ⦂ A → M —→* M' → ∅ ⊢ M' ⦂ A
—→*-pres ⊢M (M ∎)                  = ⊢M
—→*-pres ⊢M (M —→⟨ M—→M' ⟩ M'—→*N) = —→*-pres (preservation ⊢M M—→M') M'—→*N
```

Determinism implies confluence.

```agda
confluence : ∀ {n} {L M M' : Term n}
  → L —→* M → L —→* M'
    ------------------------------
  → ∃[ N ] (M —→* N) × (M' —→* N)
confluence (_ ∎)                L—→*M'                = _ , L—→*M' , (_ ∎)
confluence (_ —→⟨ L→L₁ ⟩ L₁→*M) (_ ∎)                 = _ , (_ ∎) , (_ —→⟨ L→L₁ ⟩ L₁→*M)
confluence (_ —→⟨ L→L₁ ⟩ L₁→*M) (_ —→⟨ L→L₂ ⟩ L₂→*M') rewrite —→-determ L→L₁ L→L₂ = confluence L₁→*M L₂→*M'
```

A few congruence lemmas:

```agda
appL-cong : ∀ {n} {M M' N : Term n}
  → M —→* M'
    -----------------
  → M · N —→* M' · N
appL-cong (_ ∎)                   = _ ∎
appL-cong (_ —→⟨ M—→M₁ ⟩ M₁—→*M') = step—→ _ (appL-cong M₁—→*M') (ξ-app₁ M—→M₁)

appR-cong : ∀ {n M} {N N' : Term n}
  → N —→* N'
    -------------------------
  → (ƛ M) · N —→* (ƛ M) · N'
appR-cong (_ ∎)                   = _ ∎
appR-cong (_ —→⟨ N—→N₁ ⟩ N₁—→*N') = step—→ _ (appR-cong N₁—→*N') (ξ-app₂ N—→N₁)

if-cong : ∀ {n} {L L' M N : Term n}
  → L —→* L'
    -----------------------
  → if L M N —→* if L' M N
if-cong (_ ∎)                   = _ ∎
if-cong (_ —→⟨ L—→L₁ ⟩ L₁—→*L') = step—→ _ (if-cong L₁—→*L') (ξ-if L—→L₁)
```
