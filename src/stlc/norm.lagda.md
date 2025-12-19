---
title: Normalization
--- 

> This part mainly follows the note [An Introduction to Logical Relations](https://cs.au.dk/~birke/papers/AnIntroductionToLogicalRelations.pdf)
> 
> You may also want to checkout the lecture note [OPLSS 2023: Logical Relations](https://www.cs.uoregon.edu/research/summerschool/summer23/_lectures/Logical_Relations_Notes.pdf)
>
> Or the chapter [Normalization of STLC](https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html) from Programming Language Foundations

```agda
module stlc.norm where
```

Here we consider the (weak) normalization for stlc. Please refer to the notes above for motivation and explanation :P.

## Imports

```agda
open import stlc.base
open import stlc.prop
open import stlc.subst
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

## Definitions

A term halts if there exists a reduction sequence that reduces it to value.

```agda
data Halts {n} (M : Term n) : Set where
  halts : ∀ {N}
    → M —→* N
    → Value N
      --------
    → Halts M
```

The logical relation for normalization:

```agda
𝒩_⟦_⟧ : Type → Term 0 → Set
𝒩 Bool  ⟦ M ⟧ = ∅ ⊢ M ⦂ Bool  × Halts M
𝒩 A ⇒ B ⟦ M ⟧ = ∅ ⊢ M ⦂ A ⇒ B × Halts M × (∀ {N} → 𝒩 A ⟦ N ⟧ → 𝒩 B ⟦ M · N ⟧)
```

Substitution of normalizing terms:

```agda
_⊨_ : ∀ {n} → (Fin n → Term 0) → Context n → Set
σ ⊨ Γ = ∀ {x B} → Γ ∋ x ⦂ B → 𝒩 B ⟦ σ x ⟧
```

## Auxiliary Lemmas

Normalizing terms are well typed (directly encoded in the logical predicate).

```agda
𝒩→⊢ : ∀ {M A} → 𝒩 A ⟦ M ⟧ → ∅ ⊢ M ⦂ A
𝒩→⊢ {A = Bool}  (⊢M , _) = ⊢M
𝒩→⊢ {A = A ⇒ B} (⊢M , _) = ⊢M
```

The substitution that closes the term with normalizing term is well typed.

Note that, since we are using _parallel substitution_, there is no need to define
extra structures of simultaneous substitution for single substitution like in 
the normalization chapter of [*PLF*](https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html).

```agda
⊢subst : ∀ {n} {Γ : Context n} {σ M A}
  → Γ ⊢ M ⦂ A → σ ⊨ Γ
    ------------------
  → ∅ ⊢ subst σ M ⦂ A
⊢subst ⊢M σ⊨Γ = ty-subst ⊢M (λ x → 𝒩→⊢ (σ⊨Γ x))
```

Small step preserves halting (at both directions):

```agda
—→-Halts : ∀ {M M' : Term 0} → M —→ M' → Halts M → Halts M'
—→-Halts M—→M' (halts (_ ∎) VN)                    = ⊥-elim (V-¬—→ VN M—→M')
—→-Halts M—→M' (halts (_ —→⟨ M—→M'' ⟩ M''—→*N) VN) rewrite —→-determ M—→M' M—→M'' = halts M''—→*N VN

—→-Halts' : ∀ {M M' : Term 0} → M —→ M' → Halts M' → Halts M
—→-Halts' M—→M' (halts (_ ∎) VN)                 = halts (step—→ _ (_ ∎) M—→M') VN
—→-Halts' M—→M' (halts (_ —→⟨ M'—→M ⟩ M—→*N) VN) = halts (_ —→⟨ M—→M' ⟩ _ —→⟨ M'—→M ⟩ M—→*N) VN
```

Small step preserves normalization:

```agda
—→-𝒩 : ∀ {M M' A} → M —→ M' → 𝒩 A ⟦ M ⟧ → 𝒩 A ⟦ M' ⟧
—→-𝒩 {A = Bool}  M—→M' (⊢M , HM)     = preservation ⊢M M—→M' , —→-Halts M—→M' HM
—→-𝒩 {A = A ⇒ B} M—→M' (⊢M , HM , k) = preservation ⊢M M—→M' , —→-Halts M—→M' HM , λ z → —→-𝒩 (ξ-app₁ M—→M') (k z)

—→-𝒩' : ∀ {M M' A} → ∅ ⊢ M ⦂ A → M —→ M' → 𝒩 A ⟦ M' ⟧ → 𝒩 A ⟦ M ⟧
—→-𝒩' {A = Bool}  ⊢M M—→M' (⊢M' , HM')     = ⊢M , —→-Halts' M—→M' HM'
—→-𝒩' {A = A ⇒ B} ⊢M M—→M' (⊢M' , HM' , k) = ⊢M , —→-Halts' M—→M' HM' , λ z → —→-𝒩' (⊢app ⊢M (𝒩→⊢ z)) (ξ-app₁ M—→M') (k z)
```

Multi step preserves normalization:

```agda
—→*-𝒩 : ∀ {M M' A} → M —→* M' → 𝒩 A ⟦ M ⟧ → 𝒩 A ⟦ M' ⟧
—→*-𝒩 (_ ∎)                  nn = nn
—→*-𝒩 (_ —→⟨ M—→M' ⟩ M'—→*N) nn = —→*-𝒩 M'—→*N (—→-𝒩 M—→M' nn)

—→*-𝒩' : ∀ {M M' A} → ∅ ⊢ M ⦂ A → M —→* M' → 𝒩 A ⟦ M' ⟧ → 𝒩 A ⟦ M ⟧
—→*-𝒩' ⊢M (_ ∎)                  nn = nn
—→*-𝒩' ⊢M (_ —→⟨ M—→M' ⟩ M'—→*N) nn = —→-𝒩' ⊢M M—→M' (—→*-𝒩' (preservation ⊢M M—→M') M'—→*N nn)
```

## Adequacy

Normalizing term halts. This is encoded in the logical relation predicate.

```agda
𝒩-halts : ∀ {M A} → 𝒩 A ⟦ M ⟧ → Halts M
𝒩-halts {A = Bool}  (⊢M , HM)        = HM
𝒩-halts {A = A ⇒ B} (⊢M , nn' , HMN) = nn'
```

## Fundamental Property

Well typed term is normalizing:

```agda
⊢𝒩 : ∀ {n} {Γ : Context n} {σ : Fin n → Term 0} {M A}
  → Γ ⊢ M ⦂ A → σ ⊨ Γ
    ------------------
  → 𝒩 A ⟦ subst σ M ⟧
```

- Case for variable, this is encoded in the definition.

```agda
⊢𝒩 (⊢var x) σ⊨Γ = σ⊨Γ x
```

- Case for lambda abstraction, we need to show that the term after substitution is also normalizing.

```agda
⊢𝒩 {σ = σ} {M = ƛ M} {A = A ⇒ B} (⊢abs ⊢M) σ⊨Γ = ⊢subst (⊢abs ⊢M) σ⊨Γ , halts (subst σ (ƛ M) ∎) V-abs , H
  where
    H : ∀ {N} → 𝒩 A ⟦ N ⟧ → 𝒩 B ⟦ (ƛ subst (exts σ) M) · N ⟧
    H {N} nn with halts {N = N'} N—→*N' VN' ← 𝒩-halts nn
      = —→*-𝒩' (⊢app (⊢subst (⊢abs ⊢M) σ⊨Γ) (𝒩→⊢ nn)) lemma (⊢𝒩 ⊢M (λ { Z → —→*-𝒩 N—→*N' nn ; (S x) → σ⊨Γ x }))
      where
        lemma : (ƛ subst (exts σ) M) · N —→* subst (N' • σ) M
        lemma rewrite sub-ext-sub {σ = σ} {M = M} {N = N'}
          = —→*-trans (appR-cong N—→*N') ((ƛ subst (exts σ) M) · N' —→⟨ β-abs VN' ⟩ (subst (exts σ) M [ N' ]) ∎)
```

- Case for application, normalization is encoded in the logical relation predicate.

```agda
⊢𝒩 (⊢app ⊢M ⊢N) σ⊨Γ with ⊢σM , HσM , H ← ⊢𝒩 ⊢M σ⊨Γ = H (⊢𝒩 ⊢N σ⊨Γ)
```

- Case for `true` and `false`.

```agda
⊢𝒩 {σ = σ} ⊢true  σ⊨Γ = ⊢true , halts (subst σ true ∎) V-true
⊢𝒩 {σ = σ} ⊢false σ⊨Γ = ⊢false , halts (subst σ false ∎) V-false
```

- Case for `if`, we know that the condition `L` is normalizing, so it will reduce to either `true` or `false`.
Then we can proceed with either branch.

```agda
⊢𝒩 {σ = σ} {M = if L M N} {A = A} (⊢if ⊢L ⊢M ⊢N) σ⊨Γ with ⊢𝒩 ⊢L σ⊨Γ
... | ⊢σL , halts {N = L'} L—→*L' VL 
    with Canonical-Bool (—→*-pres ⊢σL L—→*L') VL
... | inj₁ refl = —→*-𝒩' (⊢if ⊢σL (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ))
                         (—→*-trans (if-cong L—→*L') (if true (subst σ M) (subst σ N) —→⟨ β-if₁ ⟩ subst σ M ∎)) 
                         (⊢𝒩 ⊢M σ⊨Γ)
... | inj₂ refl = —→*-𝒩' (⊢if ⊢σL (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ))
                         (—→*-trans (if-cong L—→*L') (if false (subst σ M) (subst σ N) —→⟨ β-if₂ ⟩ subst σ N ∎)) 
                         (⊢𝒩 ⊢N σ⊨Γ)
```

## Normalization

```agda
norm : ∀ {M A} → ∅ ⊢ M ⦂ A → Halts M
norm {M = M} ⊢M with 𝒩-halts (⊢𝒩 {σ = ids} ⊢M (λ ()))
... | HM rewrite sub-id {M = M} = HM
```