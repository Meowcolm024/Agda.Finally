---
title: Basics
---

```agda
module stlc.base where
```

Definition of the simply typed lambda calculus with boolean, using well scoped de bruijn index.

## Imports

```agda
open import Data.Nat using (ℕ; zero; suc; _≤?_)
open import Data.Fin using (Fin; zero; suc; fromℕ<)
open import Relation.Nullary.Decidable using (True; toWitness)
```

## Syntax

Here we consider a simply typed lambda calculus with *Booleans*.
It is a bit more interesting than the one with only a base type, and yet
simplier than others with types like `Nat`.

We define *types* as follows:

```agda
infixr 7 _⇒_

data Type : Set where
  Bool : Type
  _⇒_  : Type → Type → Type
```

The definition of *term* is indexed by its "scope" `n : ℕ`.
The scope indicates the *number of free variables* in the term.
So a term `M : Term 0` is closed and `N : Term 1` (may) have
one unbounded variable.

Note the

```agda
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data Term (n : ℕ) : Set where
  `_    : Fin n → Term n                    -- variable
  ƛ_    : Term (suc n) → Term n             -- lambda abstraction
  _·_   : Term n → Term n → Term n          -- function application
  true  : Term n
  false : Term n
  if    : Term n → Term n → Term n → Term n -- if-then-else
```

The case for variable and lambda abstraction is slightly more interesting.

- The variable constructor takes an *de Bruijn index* `x : Fin n` (which can be seen as a number in the set `{ m | m < n }`), so a variable index is always within the scope of the term.
- The lambda constructor takes a `M : Term (suc n)`, which is its body with scope extended by 1 (i.e. the variable `x` in `λ x → M`).

```agda
infix  9 #_
-- a shorthand to write (# 2) instead of (` suc (suc zero))
#_ : ∀ {n} (m : ℕ) → {m<n : True (suc m ≤? n)} → Term n
#_ m {m<n} = ` fromℕ< (toWitness m<n)
```

The definition of *typing context* is just a list (or *vector*) indexed by its length (`n : ℕ`).

```agda
infixl 5 _,-_

data Context : ℕ → Set where
  ∅    : Context 0
  _,-_ : ∀ {n} → Context n → Type → Context (suc n)
```

The *context lookup* is a relation between the context, de Bruijn index,
and its associated type.

```agda
infix  3 _∋_⦂_

data _∋_⦂_ : ∀ {n} → Context n → Fin n → Type → Set where

  Z : ∀ {n A} {Γ : Context n}
      ------------------
    → Γ ,- A ∋ zero ⦂ A

  S : ∀ {n x A B} {Γ : Context n}
    → Γ ∋ x ⦂ A
      -------------------
    → Γ ,- B ∋ suc x ⦂ A
```

## Renaming and Substitution

Renaming and substitution are almost identical to the
ones using unscoped or well-typed (intrinsically typed) de Bruijn index.

Checkout [Autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf)
for the unscoped one and [PLFA](https://plfa.github.io/DeBruijn/) for the intrinsically typed one for explanation :P

```agda
ext : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : ∀ {n m} → (Fin n → Fin m) → Term n → Term m
rename ρ (` x)      = ` ρ x
rename ρ (ƛ M)      = ƛ rename (ext ρ) M
rename ρ (M · N)    = (rename ρ M) · (rename ρ N)
rename ρ true       = true
rename ρ false      = false
rename ρ (if L M N) = if (rename ρ L) (rename ρ M) (rename ρ N)

exts : ∀ {n m} → (Fin n → Term m) → Fin (suc n) → Term (suc m)
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

subst : ∀ {n m} → (Fin n → Term m) → Term n → Term m
subst σ (` x)      = σ x
subst σ (ƛ M)      = ƛ subst (exts σ) M
subst σ (M · N)    = (subst σ M) · (subst σ N)
subst σ true       = true
subst σ false      = false
subst σ (if L M N) = if (subst σ L) (subst σ M) (subst σ N)
```

Single substitution is just a special case of the more general one.

```agda
subst-zero : ∀ {n} → Term n → (Fin (suc n) → Term n)
subst-zero N zero    = N
subst-zero N (suc x) = ` x

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
M [ N ] = subst (subst-zero N) M
```

## Typing

The typing rules are fairly standard and not that interesting.

```agda
infix  4 _⊢_⦂_

data _⊢_⦂_ {n} : Context n → Term n → Type → Set where

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      ------------
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {Γ A B M}
    → Γ ,- A ⊢ M ⦂ B
      ----------------
    → Γ ⊢ ƛ M ⦂ A ⇒ B

  ⊢app : ∀ {Γ A B M N}
    → Γ ⊢ M ⦂ A ⇒ B
    → Γ ⊢ N ⦂ A
      --------------
    → Γ ⊢ M · N ⦂ B

  ⊢true : ∀ {Γ}
      ----------------
    → Γ ⊢ true ⦂ Bool

  ⊢false : ∀ {Γ}
      -----------------
    → Γ ⊢ false ⦂ Bool

  ⊢if : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ Bool
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      -----------------
    → Γ ⊢ if L M N ⦂ A
```

## Reduction

Here we consider a call-by-value small-step operational semantic,
and we start with the definition of _Value_ first:

```agda
data Value {n} : Term n → Set where
  V-abs   : ∀ {M} → Value (ƛ M)
  V-true  : Value true
  V-false : Value false
```

And the actual reduction:

```agda
infix  2 _—→_

data _—→_ {n} : Term n → Term n → Set where

  ξ-app₁ : ∀ {M M' N}
    → M —→ M'
      ----------------
    → M · N —→ M' · N

  ξ-app₂ : ∀ {M N N'}
    → N —→ N'
      ------------------------
    → (ƛ M) · N —→ (ƛ M) · N'

  β-abs : ∀ {M N}
    → Value N
      ---------------------
    → (ƛ M) · N —→ M [ N ]

  ξ-if : ∀ {L L' M N}
    → L —→ L'
      ----------------------
    → if L M N —→ if L' M N

  β-if₁ : ∀ {M N}
      -----------------
    → if true M N —→ M

  β-if₂ : ∀ {M N}
      ------------------
    → if false M N —→ N
```

Finally, we define the multi-step reduction as a reflexive and transitive closure 
of the small-step relation.

```agda
module multistep where
  infix  2 _—→*_
  infix  1 begin_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—→*_ {n} : Term n → Term n → Set where
    _∎ : ∀ (M : Term n)
        ------------------
      → M —→* M

    step—→ : ∀ (L : Term n) {M N}
      → M —→* N
      → L —→ M
        --------
      → L —→* N

  pattern _—→⟨_⟩_ L LM MN = step—→ L MN LM

  begin_ : ∀ {n} {M N : Term n} → M —→* N → M —→* N
  begin st = st
```