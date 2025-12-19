---
title: Natural Semantics
---

> This part is adapted from [PLFA:BigStep](https://plfa.github.io/BigStep/)

```agda
module stlc.natural where
```

Here we consider the closure (environment) based big step semantic.

The definitions and proofs in this part is almost identical to the one in *PLFA*, 
please refer back to *PLFA* for detailed explanation :P.

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
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_∘_)
```

## Closures

The closure `Clos` will be the final result of our natural semantic.
It can be `true`, `false` or `clos` of a term `M` with a closure environment `γ`.

And we define the closure environment `ClosEnv` to be a function 
(instead of an inductive type).

Note that we do not restrict the term inside the closure to be a lambda here.

```agda
ClosEnv : (n : ℕ) → Set

data Clos : Set where
  true  : Clos
  false : Clos
  clos  : ∀ {n} → Term n → ClosEnv n → Clos

ClosEnv n = Fin n → Clos
```

Closure environment lookup:

```agda
∅' : ClosEnv 0
∅' ()

_,'_ : ∀ {n} → ClosEnv n → Clos → ClosEnv (suc n)
(γ ,' c) zero    = c
(γ ,' c) (suc x) = γ x
```

## Natural Semantic

```agda
infix  2 _⊢_⇓_

data _⊢_⇓_ : ∀ {n} → ClosEnv n → Term n → Clos → Set where

  ⇓-var : ∀ {n} {γ : ClosEnv n} {x V}
    → γ x ≡ V
      ------------
    → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀ {n} {γ : ClosEnv n} {M}
      -----------------------
    → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀ {n m} {γ : ClosEnv n} {δ : ClosEnv m} {L M N U V}
    → γ ⊢ L ⇓ clos (ƛ N) δ
    → γ ⊢ M ⇓ U
    → (δ ,' U) ⊢ N ⇓ V
      ---------------------
    → γ ⊢ L · M ⇓ V

  ⇓-true : ∀ {n} {γ : ClosEnv n}
      ----------------
    → γ ⊢ true ⇓ true

  ⇓-false : ∀ {n} {γ : ClosEnv n}
      ------------------
    → γ ⊢ false ⇓ false

  ⇓-if₁ : ∀ {n} {γ : ClosEnv n} {L M N V}
    → γ ⊢ L ⇓ true
    → γ ⊢ M ⇓ V
      -----------------
    → γ ⊢ if L M N ⇓ V

  ⇓-if₂ : ∀ {n} {γ : ClosEnv n} {L M N V}
    → γ ⊢ L ⇓ false
    → γ ⊢ N ⇓ V
      -----------------
    → γ ⊢ if L M N ⇓ V
```

## Basic Properties of Natural Semantic

The reduction is deterministic:

```agda
⇓-determ : ∀ {n} {γ : ClosEnv n} {M V V'}
  → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
    -----------------------
  → V ≡ V'
⇓-determ (⇓-var refl)          (⇓-var refl)       = refl
⇓-determ ⇓-lam                 ⇓-lam              = refl
⇓-determ (⇓-app L⇓c M⇓U N⇓V) (⇓-app L⇓c' M⇓U' N⇓V')
  with refl ← ⇓-determ L⇓c L⇓c' | refl ← ⇓-determ M⇓U M⇓U'
  with refl ← ⇓-determ N⇓V N⇓V'                   = refl
⇓-determ ⇓-true              ⇓-true               = refl
⇓-determ ⇓-false             ⇓-false              = refl
⇓-determ (⇓-if₁ L⇓true M⇓V)  (⇓-if₁ _ M⇓V')       = ⇓-determ M⇓V M⇓V'
⇓-determ (⇓-if₁ L⇓true M⇓V)  (⇓-if₂ L⇓false N⇓V') with () ← ⇓-determ L⇓true L⇓false
⇓-determ (⇓-if₂ L⇓false N⇓V) (⇓-if₁ L⇓true M⇓V')  with () ← ⇓-determ L⇓false L⇓true
⇓-determ (⇓-if₂ L⇓false N⇓V) (⇓-if₂ _ N⇓V')       = ⇓-determ N⇓V N⇓V'
```

## Relating Natural Semantic and Small Step

Relating closure environment and substitution, closures and values:

```agda
_≈_  : Clos → Term 0 → Set
_≈ₑ_ : ∀ {n} → ClosEnv n → (Fin n → Term 0) → Set

true               ≈ true  = ⊤
false              ≈ false = ⊤
(clos {n} (ƛ M) γ) ≈ N     = Σ[ σ ∈ (Fin n → Term 0) ] (γ ≈ₑ σ) × (N ≡ subst σ (ƛ M))
_                  ≈ _     = ⊥

γ ≈ₑ σ = ∀ x → (γ x) ≈ (σ x)

Clos≈Value : ∀ {V : Clos} {M : Term 0} → V ≈ M → Value M
Clos≈Value {true}          {true}  V≈M = V-true
Clos≈Value {false}         {false} V≈M = V-false
Clos≈Value {clos (ƛ M') γ} {ƛ M}   V≈M = V-abs
```

Relation closure environment extension and substitution extension:

```agda
≈ₑ-ext : ∀ {n} {γ : ClosEnv n} {σ : Fin n → Term 0} {N V}
  → γ ≈ₑ σ → V ≈ N
    ----------------------------
  → (γ ,' V) ≈ₑ (ext-subst σ N)
≈ₑ-ext             γ≈ₑσ V≈N zero    = V≈N
≈ₑ-ext {σ = σ} {N} γ≈ₑσ V≈N (suc x) rewrite subst-zero-exts {σ = σ} {M = N} {x = x} = γ≈ₑσ x
```

Natural semantic implies multi step reduction to value:

```agda
⇓→—→*×≈ : ∀ {n} {γ : ClosEnv n} {σ : Fin n → Term 0} {M V}
  → γ ⊢ M ⇓ V → γ ≈ₑ σ
    ------------------------------------------
  → Σ[ N ∈ Term 0 ] (subst σ M —→* N) × V ≈ N

⇓→—→*×≈ {σ = σ} (⇓-var {x = x} refl) γ≈ₑσ = subst σ (` x) , (subst σ (` x) ∎) , γ≈ₑσ x
⇓→—→*×≈ {σ = σ} {V = clos (ƛ M) γ} ⇓-lam γ≈ₑσ = subst σ (ƛ M) , (subst σ (ƛ M) ∎) , σ , γ≈ₑσ , refl
⇓→—→*×≈ {σ = σ} (⇓-app {L = L} {M = M} {N = N} L⇓c M⇓U N⇓V) γ≈ₑσ
    with (ƛ L' , L—→*L' , σ' , k , refl) ← ⇓→—→*×≈ L⇓c γ≈ₑσ 
    |    (M' , M—→*M' , U≈M') ← ⇓→—→*×≈ M⇓U γ≈ₑσ
    with (N' , N—→*N' , V≈N') ← ⇓→—→*×≈ {σ = ext-subst σ' M'} N⇓V (λ x → ≈ₑ-ext {σ = σ'} k U≈M' x)
    = N' , σLM→*N' , V≈N'
    where
      σLM→*N' : subst σ L · subst σ M —→* N'
      σLM→*N' = —→*-trans (appL-cong L—→*L') (—→*-trans (appR-cong M—→*M')
        (_ —→⟨ β-abs (Clos≈Value U≈M') ⟩ Eq.subst (_—→* N') (Eq.sym (sub-sub {M = N} {σ₁ = exts σ'} {σ₂ = subst-zero M'})) N—→*N'))
⇓→—→*×≈ {σ = σ} ⇓-true γ≈ₑσ = true , (subst σ true ∎) , tt
⇓→—→*×≈ {σ = σ} ⇓-false γ≈ₑσ = false , (subst σ false ∎) , tt
⇓→—→*×≈ (⇓-if₁ M⇓true M⇓V) γ≈ₑσ 
    with (true , L—→*true , tt) ← ⇓→—→*×≈ M⇓true γ≈ₑσ 
    |    (M' , M—→*M' , V≈M') ← ⇓→—→*×≈ M⇓V γ≈ₑσ
    = M' , —→*-trans (if-cong L—→*true) (_ —→⟨ β-if₁ ⟩ M—→*M') , V≈M'
⇓→—→*×≈ (⇓-if₂ M⇓false N⇓V) γ≈ₑσ  
    with (false , L—→*false , tt) ← ⇓→—→*×≈ M⇓false γ≈ₑσ 
    |    (N' , M—→*N' , V≈N') ← ⇓→—→*×≈ N⇓V γ≈ₑσ
    = N' , —→*-trans (if-cong L—→*false) (_ —→⟨ β-if₂ ⟩ M—→*N') , V≈N'
```

Value reduces to value:

```agda
V⇓-≈ : ∀ {M V} → Value M → ∅' ⊢ M ⇓ V → V ≈ M
V⇓-≈ (V-abs {M = M}) ⇓-lam  = ids , (λ ()) , lemma
  where
    lemma : ƛ M ≡ ƛ subst (exts ids) M
    lemma = Eq.cong ƛ_ (Eq.subst (λ σ → M ≡ subst σ M) (Eq.sym exts-ids) (Eq.sym sub-id))
V⇓-≈ V-true         ⇓-true  = tt
V⇓-≈ V-false        ⇓-false = tt
```