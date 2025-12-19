---
title: Bigstep
---

```agda
module stlc.bigstep where
```

Here we consider a substitution-based big step semantic.

## Imports

```agda
open import stlc.base
open import stlc.prop
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

## Big Step Semantic

```agda
infix  2 _⇓_

data _⇓_ {n} : Term n → Term n → Set where

    ⇓-abs : ∀ {M : Term (suc n)}
          ----------
        → ƛ M ⇓ ƛ M

    ⇓-app : ∀ {M'} {M N N' V : Term n}
        → M ⇓ ƛ M'
        → N ⇓ N'
        → M' [ N' ] ⇓ V
          --------------
        → M · N ⇓ V

    ⇓-true : true ⇓ true

    ⇓-false : false ⇓ false

    ⇓-if₁ : ∀ {L M N V : Term n}
        → L ⇓ true
        → M ⇓ V
          -------------
        → if L M N ⇓ V

    ⇓-if₂ : ∀ {L M N V : Term n}
        → L ⇓ false
        → N ⇓ V
          -------------
        → if L M N ⇓ V 
```

## Basic Properties of Big Step Semantic

Big step preserves typing:

```agda
⇓-pres : ∀ {A M V} → ∅ ⊢ M ⦂ A → M ⇓ V → ∅ ⊢ V ⦂ A
⇓-pres (⊢abs ⊢M)      ⇓-abs                       = ⊢abs ⊢M
⇓-pres (⊢app ⊢M ⊢N)   (⇓-app M⇓ƛM' N⇓N' M'[N']⇓V) with (⊢abs ⊢M') ← ⇓-pres ⊢M M⇓ƛM'
                                                  = ⇓-pres (ty-subst ⊢M' λ { Z → ⇓-pres ⊢N N⇓N' }) M'[N']⇓V
⇓-pres ⊢true          ⇓-true                      = ⊢true
⇓-pres ⊢false         ⇓-false                     = ⊢false
⇓-pres (⊢if ⊢L ⊢M ⊢N) (⇓-if₁ L⇓true M⇓V)          = ⇓-pres ⊢M M⇓V
⇓-pres (⊢if ⊢L ⊢M ⊢N) (⇓-if₂ L⇓false N⇓V)         = ⇓-pres ⊢N N⇓V
```

Value reduces to itself:

```agda
V-⇓ : ∀ {M : Term 0} → Value M → M ⇓ M
V-⇓ V-abs   = ⇓-abs
V-⇓ V-true  = ⇓-true
V-⇓ V-false = ⇓-false
```

Big step reduces to value:

```agda
⇓-V : ∀ {A M V} → ∅ ⊢ M ⦂ A → M ⇓ V → Value V
⇓-V (⊢abs ⊢M)      ⇓-abs                       = V-abs
⇓-V (⊢app ⊢M ⊢N)   (⇓-app M⇓ƛM' N⇓N' M'[N']⇓V) with (⊢abs ⊢M') ← ⇓-pres ⊢M M⇓ƛM'
                                               = ⇓-V (ty-subst ⊢M' λ { Z → ⇓-pres ⊢N N⇓N' }) M'[N']⇓V
⇓-V ⊢true          ⇓-true                      = V-true
⇓-V ⊢false         ⇓-false                     = V-false
⇓-V (⊢if ⊢L ⊢M ⊢N) (⇓-if₁ L⇓true M⇓V)          = ⇓-V ⊢M M⇓V
⇓-V (⊢if ⊢L ⊢M ⊢N) (⇓-if₂ L⇓false N⇓V)         = ⇓-V ⊢N N⇓V
```

Big step is deterministic:

```agda
⇓-determ : ∀ {M V V' : Term 0}
    → M ⇓ V → M ⇓ V'
      ---------------
    → V ≡ V' 
⇓-determ ⇓-abs                       ⇓-abs                = refl
⇓-determ (⇓-app M⇓ƛM₁ N⇓N₁ M₁[N₁]⇓V) (⇓-app M⇓ƛM₂ N⇓N₂ M₂[N₂]⇓V') 
    with refl ← ⇓-determ M⇓ƛM₁ M⇓ƛM₂ | refl ← ⇓-determ N⇓N₁ N⇓N₂ 
    with refl ← ⇓-determ M₁[N₁]⇓V M₂[N₂]⇓V'               = refl
⇓-determ ⇓-true                      ⇓-true               = refl
⇓-determ ⇓-false                     ⇓-false              = refl
⇓-determ (⇓-if₁ L⇓true M⇓V)          (⇓-if₁ _ M⇓V')       = ⇓-determ M⇓V M⇓V'
⇓-determ (⇓-if₁ L⇓true M⇓V)          (⇓-if₂ L⇓false M⇓V') = contradiction (⇓-determ L⇓true L⇓false) λ ()
⇓-determ (⇓-if₂ L⇓false N⇓V)         (⇓-if₁ L⇓true M⇓V')  = contradiction (⇓-determ L⇓false L⇓true) λ ()
⇓-determ (⇓-if₂ L⇓false N⇓V)         (⇓-if₂ _ N⇓V')       = ⇓-determ N⇓V N⇓V'
```

## Relating Small Step and Big Step

Big step implies multi step reduction to value (with the lemma `⇓-V`):

```agda
⇓≈—→* : ∀ {A M V} 
    → ∅ ⊢ M ⦂ A → M ⇓ V 
      ------------------
    → M —→* V
⇓≈—→* (⊢abs ⊢M)    ⇓-abs                       = _ ∎
⇓≈—→* (⊢app ⊢M ⊢N) (⇓-app M⇓ƛM' N⇓N' M'[N']⇓V) with (⊢abs ⊢M') ← ⇓-pres ⊢M M⇓ƛM'
    = —→*-trans (appL-cong (⇓≈—→* ⊢M M⇓ƛM')) 
        (—→*-trans (appR-cong (⇓≈—→* ⊢N N⇓N'))
        (_ —→⟨ β-abs (⇓-V ⊢N N⇓N') ⟩ ⇓≈—→* (ty-subst ⊢M' λ { Z → ⇓-pres ⊢N N⇓N' }) M'[N']⇓V))
⇓≈—→* ⊢true          ⇓-true                    = true ∎
⇓≈—→* ⊢false         ⇓-false                   = false ∎
⇓≈—→* (⊢if ⊢L ⊢M ⊢N) (⇓-if₁ L⇓true M⇓V)        = —→*-trans (if-cong (⇓≈—→* ⊢L L⇓true)) (_ —→⟨ β-if₁ ⟩ ⇓≈—→* ⊢M M⇓V)
⇓≈—→* (⊢if ⊢L ⊢M ⊢N) (⇓-if₂ L⇓false N⇓V)       = —→*-trans (if-cong (⇓≈—→* ⊢L L⇓false)) (_ —→⟨ β-if₂ ⟩ ⇓≈—→* ⊢N N⇓V)
```

Before showing multi step to value implies big step, we prove the following lemma first:

```agda
—→≈⇓ : ∀ {A M M' V}
    → ∅ ⊢ M ⦂ A 
    → M —→ M' → M' ⇓ V
      -----------------
    → M ⇓ V
—→≈⇓ (⊢app ⊢M ⊢N)        (ξ-app₁ M—→M') (⇓-app M'⇓ƛM'' N⇓N' M''[N']⇓V) = ⇓-app (—→≈⇓ ⊢M M—→M' M'⇓ƛM'') N⇓N' M''[N']⇓V
—→≈⇓ (⊢app ⊢M ⊢N)        (ξ-app₂ M—→M') (⇓-app M'⇓ƛM'' N⇓N' M''[N']⇓V) = ⇓-app M'⇓ƛM'' (—→≈⇓ ⊢N M—→M' N⇓N') M''[N']⇓V
—→≈⇓ (⊢app (⊢abs ⊢M) ⊢N) (β-abs VN)     M'⇓V                           = ⇓-app ⇓-abs (V-⇓ VN) M'⇓V
—→≈⇓ (⊢if ⊢L ⊢M ⊢N)      (ξ-if L—→L')   (⇓-if₁ L'⇓true M⇓V)            = ⇓-if₁ (—→≈⇓ ⊢L L—→L' L'⇓true) M⇓V
—→≈⇓ (⊢if ⊢L ⊢M ⊢N)      (ξ-if L—→L')   (⇓-if₂ L'⇓false N⇓V)           = ⇓-if₂ (—→≈⇓ ⊢L L—→L' L'⇓false) N⇓V
—→≈⇓ (⊢if ⊢true ⊢M ⊢N)   β-if₁          M'⇓V                           = ⇓-if₁ ⇓-true M'⇓V
—→≈⇓ (⊢if ⊢false ⊢M ⊢N)  β-if₂          M'⇓V                           = ⇓-if₂ ⇓-false M'⇓V
```

Finally, we can show that multi step reduction to value implies big step:

```agda
—→*≈⇓ : ∀ {A M V}
    → ∅ ⊢ M ⦂ A 
    → M —→* V → Value V
      ------------------
    → M ⇓ V
—→*≈⇓ ⊢M (M ∎)                VV = V-⇓ VV
—→*≈⇓ ⊢M (L —→⟨ L—→M ⟩ M—→*V) VV = —→≈⇓ ⊢M L—→M (—→*≈⇓ (preservation ⊢M L—→M) M—→*V VV)
```
