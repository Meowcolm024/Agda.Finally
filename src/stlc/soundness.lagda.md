---
title: Semantic Typing
---

> This part mainly follows the note [An Introduction to Logical Relations](https://cs.au.dk/~birke/papers/AnIntroductionToLogicalRelations.pdf)
> 
> You may also want to checkout the lecture note [OPLSS 2023: Logical Relations](https://www.cs.uoregon.edu/research/summerschool/summer23/_lectures/Logical_Relations_Notes.pdf)
> 
> Or the [Rocq formalization](https://github.com/tmoux/logical-relations)

```agda
module stlc.soundness where
```

Here we consider the _semantic type soundness (safety)_ of stlc. Please refer to the notes above for motivation and explanation :P.

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
open import Relation.Nullary using (¬_; contradiction; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
```

## Definitions

Definition of **type safety**: a term is either a value or it can make a step.

```agda
Safe : Term 0 → Set
Safe M = ∀ M' → M —→* M' → Value M' ⊎ ∃[ N ] (M' —→ N)
```

A term is *irreducible* if it cannot step.

```agda
infix  6 —↛_

—↛_ : Term 0 → Set
—↛_ M = ∀ M' → ¬ (M —→ M')
```

The definition of *semantic value* and *semantic expression*:
- The semantic value of type `Bool` is `either` true or `false`.
- The semantic value of function type is a lambda, which is a semantic expression when applying a semantic value of another term `N`.
- A semantic expression is a term that can be reduced to a semantic value.

```agda
𝒱⟦_⟧ : Type → Term 0 → Set
ℰ⟦_⟧ : Type → Term 0 → Set

𝒱⟦ Bool  ⟧ true  = ⊤
𝒱⟦ Bool  ⟧ false = ⊤
𝒱⟦ A ⇒ B ⟧ (ƛ M) = ∀ N → 𝒱⟦ A ⟧ N → ℰ⟦ B ⟧ (M [ N ])
𝒱⟦ _     ⟧ _     = ⊥

ℰ⟦ A ⟧ M = ∀ M' → (M —→* M') × (—↛ M') → 𝒱⟦ A ⟧ M'
```

Definition of well typed substitution of semantic values.

```agda
𝒢⟦_⟧ : ∀ {n} → Context n → (Fin n → Term 0) → Set
𝒢⟦ Γ ⟧ σ = ∀ {x A} → Γ ∋ x ⦂ A → 𝒱⟦ A ⟧ (σ x)
```

Definition of semantic typing: A term `M` has type `A` under context `Γ`, 
if it is a semantic expression of type `A` when closed by the substitution `σ`.

```agda
_⊨_⦂_ : ∀ {n} → Context n → Term n → Type → Set
Γ ⊨ M ⦂ A = ∀ σ → 𝒢⟦ Γ ⟧ σ → ℰ⟦ A ⟧ (subst σ M)
```

## Auxiliary Lemmas

Whether a term is a syntactic value is decidable:

```agda
value? : (M : Term 0) → Dec (Value M)
value? (ƛ M)      = yes V-abs
value? (M · N)    = no λ ()
value? true       = yes V-true
value? false      = yes V-false
value? (if L M N) = no λ ()
```

> TODO refactor

Whether a term is reducible is decidable:

```agda
reducible? : (M : Term 0) → Dec (∃[ M' ] (M —→ M'))
reducible? (ƛ M) = no λ ()
reducible? (M · N) with reducible? M
... | yes (M' , M→M') = yes (M' · N , ξ-app₁ M→M')
reducible? ((ƛ M) · N)  | no —↛M with reducible? N
... | yes (N' , N→N') = yes ((ƛ M) · N' , ξ-app₂ N→N')
... | no  —↛N with value? N
...   | yes VN  = yes ((M [ N ]) , β-abs VN)
...   | no  ¬VN = no λ { (_ , ξ-app₂ N→N') → —↛N (_ , N→N') ; (_ , β-abs VN) → ¬VN VN }
reducible? (M₁ · M₂ · N)     | no —↛M = no λ { (_ , ξ-app₁ M→M') → —↛M (_ , M→M') }
reducible? (true · N)        | no —↛M = no λ { (_ , ξ-app₁ M→M') → —↛M (_ , M→M') }
reducible? (false · N)       | no —↛M = no λ { (_ , ξ-app₁ M→M') → —↛M (_ , M→M') }
reducible? (if M₁ M₂ M₃ · N) | no —↛M = no λ { (_ , ξ-app₁ M→M') → —↛M (_ , M→M') }
reducible? true       = no λ ()
reducible? false      = no λ ()
reducible? (if L M N) with reducible? L
... | yes (M' , M→M') = yes (if M' M N , ξ-if M→M')
... | no  —↛M with L
...   | ƛ L₁          = no λ { (_ , ξ-if if→if') → —↛M (_ , if→if') }
...   | L₁ · L₂       = no λ { (_ , ξ-if if→if') → —↛M (_ , if→if') }
...   | true          = yes (M , β-if₁)
...   | false         = yes (N , β-if₂)
...   | if L₁ L₂ L₃   = no λ { (_ , ξ-if if→if') → —↛M (_ , if→if') }
```

Canonical value of `Bool` and function type:

```agda
𝒱⟦Bool⟧-Canonical : ∀ {M} → 𝒱⟦ Bool ⟧ M → M ≡ true ⊎ M ≡ false
𝒱⟦Bool⟧-Canonical {M = true}  VM = inj₁ refl
𝒱⟦Bool⟧-Canonical {M = false} VM = inj₂ refl

𝒱⟦⇒⟧-Canonical : ∀ {M A B} → 𝒱⟦ A ⇒ B ⟧ M → ∃[ N ] (M ≡ ƛ N)
𝒱⟦⇒⟧-Canonical {M = ƛ M} VM = M , refl
```

Multi-step of irreducible term reduces to itself.

```agda
—↛-M→*M : ∀ {M M'} → M —→* M' → —↛ M → M ≡ M'
—↛-M→*M (_ ∎)                —↛M = refl
—↛-M→*M (_ —→⟨ M→M₁ ⟩ M→*M') —↛M = ⊥-elim (—↛M _ M→M₁)
```

Syntactic value is irreducible.

```agda
V→—↛ : ∀ {M : Term 0} → Value M → —↛ M
V→—↛ V-abs   M' ()
V→—↛ V-true  M' ()
V→—↛ V-false M' ()
```

Semantic value implies syntactic value.

```agda
𝒱-V : ∀ {M A} → 𝒱⟦ A ⟧ M → Value M
𝒱-V {M = true}  {A = Bool}  VM = V-true
𝒱-V {M = false} {A = Bool}  VM = V-false
𝒱-V {M = ƛ M}   {A = A ⇒ B} VM = V-abs
```

Semantic value is irreducible.

```agda
𝒱→—↛ : ∀ {M A} → 𝒱⟦ A ⟧ M → —↛ M
𝒱→—↛ VM = V→—↛ (𝒱-V VM)
```

A few lemmas for irreducible terms that are not values:
- An irreducible application implies its lhs is irreducible (or rhs)
- An irreducible if clause implies the predicate is irreducible 

```agda
appL—↛ : ∀ {M N V} → M · N —→* V → —↛ V → ∃[ M' ] (M —→* M') × (—↛ M')
appL—↛ ((M · N) ∎)                         —↛V = M , (M ∎) , λ { M' x → —↛V (M' · N) (ξ-app₁ x) }
appL—↛ ((M · N) —→⟨ ξ-app₁ M→M' ⟩ M·N→*V)  —↛V with M' , M→*M' , —↛M' ← appL—↛ M·N→*V —↛V = M' , step—→ M M→*M' M→M' , —↛M'
appL—↛ ((M · N) —→⟨ ξ-app₂ N→N' ⟩ M·N→*V)  —↛V = appL—↛ M·N→*V —↛V
appL—↛ (((ƛ M) · N) —→⟨ β-abs VN ⟩ M·N→*V) —↛V = ƛ M , (ƛ M ∎) , λ { M' () }

appR—↛ : ∀ {M N V} → (ƛ M) · N —→* V → —↛ V → ∃[ N' ] (N —→* N') × (—↛ N')
appR—↛ (((ƛ M) · N) ∎)                        —↛V = N , (N ∎) , λ { M' x → —↛V ((ƛ M) · M') (ξ-app₂ x) }
appR—↛ (((ƛ M) · N) —→⟨ ξ-app₂ N→N' ⟩ M·N→*V) —↛V with N' , N→*N' , —↛N' ← appR—↛ M·N→*V —↛V = N' , step—→ N N→*N' N→N' , —↛N'
appR—↛ (((ƛ M) · N) —→⟨ β-abs VN ⟩ M·N→*V)    —↛V = N , (N ∎) , V→—↛ VN

if—↛ : ∀ {L M N V} → if L M N —→* V → —↛ V → ∃[ L' ] (L —→* L') × (—↛ L')
if—↛ ((if L M N) ∎)                    —↛V = L , (L ∎) , (λ M' x → —↛V (if M' M N) (ξ-if x))
if—↛ ((if L M N) —→⟨ ξ-if VL ⟩ if→*V)  —↛V with L' , L→L' , —↛L' ← if—↛ if→*V —↛V = L' , (L —→⟨ VL ⟩ L→L') , —↛L'
if—↛ ((if true M N) —→⟨ β-if₁ ⟩ M→*V)  —↛V = true , (true ∎) , λ { x () }
if—↛ ((if false M N) —→⟨ β-if₂ ⟩ N→*V) —↛V = false , (false ∎) , λ {x () }
```

Triangular property (?): 

```agda
conf—↛join : ∀ {L M M'} → L —→* M → L —→* M' → —↛ M → M' —→* M
conf—↛join L→*M L→*M' —↛M
  with N , M→*N , M'→*N ← confluence L→*M L→*M'
  with refl ← —↛-M→*M M→*N —↛M
  = M'→*N
```

## Adequacy

Semantically well typed term is safe:

```agda
⊨safe : ∀ {M A} → ∅ ⊨ M ⦂ A → Safe M
⊨safe {M = M} ⊨M M' M→*M' with reducible? M'
... | yes M'→M'' = inj₂ M'→M''
... | no  —↛M'   = inj₁ (𝒱-V (⊨M ids (λ ()) M' (⟪id⟫M→*M , λ M'' z → —↛M' (M'' , z))))
  where
    ⟪id⟫M→*M : subst ids M —→* M'
    ⟪id⟫M→*M = Eq.subst (_—→* M') (Eq.sym sub-id) M→*M'
```

## Fundamental Property

> TODO refactor

Syntactic typing implies semantic typing:

```agda
⊢-⊨ : ∀ {n} {Γ : Context n} {M A}
  → Γ ⊢ M ⦂ A
    ----------
  → Γ ⊨ M ⦂ A
```

- Case `var`

```agda
⊢-⊨ (⊢var x) σ GG M' (M→*M' , —↛M') with refl ← —↛-M→*M M→*M' (𝒱→—↛ (GG x)) = GG x
```

- Case `abs`

```agda
⊢-⊨ {M = ƛ M} (⊢abs ⊢M) σ GG M' ((ƛ ⟪σ⟫M ∎) , —↛M') N VN M'' (MN→M' , —↛M'')
  = ⊢-⊨ ⊢M (N • σ) (λ { Z → VN ; (S x) → GG x }) M'' (⟪N•σ⟫M→*M'' , —↛M'')
  where
    ⟪N•σ⟫M→*M'' : subst (N • σ) M —→* M''
    ⟪N•σ⟫M→*M'' rewrite Eq.sym (sub-ext-sub {σ = σ} {M = M} {N = N}) = MN→M'
```

- Case `app`

```agda
⊢-⊨ {M = M · N} (⊢app ⊢M ⊢N) σ GG M' (M→*M' , —↛M')
  with M₁ , σM→M₁ , —↛M₁ ← appL—↛ M→*M' —↛M'
  with VM ← ⊢-⊨ ⊢M σ GG M₁ (σM→M₁ , —↛M₁)
  with M₁' , refl ← 𝒱⟦⇒⟧-Canonical VM
  with M₁·σN→*M' ← conf—↛join M→*M' (—→*-trans (appL-cong σM→M₁) (M₁ · subst σ N ∎)) —↛M'
  with N₁ , σN→N₁ , —↛N₁ ← appR—↛ M₁·σN→*M' —↛M'
  with VN ← ⊢-⊨ ⊢N σ GG N₁ (σN→N₁ , —↛N₁)
  = VM N₁ VN M' (M₁[N₁]→*M₂ , —↛M')
  where
    M₁[N₁]→*M₂ = conf—↛join M→*M'
      (—→*-trans (appL-cong σM→M₁) (—→*-trans (appR-cong σN→N₁) (_ —→⟨ β-abs (𝒱-V VN) ⟩ (M₁' [ N₁ ]) ∎))) —↛M'
```

- Case `true` and `false`

```agda
⊢-⊨ ⊢true  σ GG M' (M→*M' , —↛M') with refl ← —↛-M→*M M→*M' (λ { _ () }) = tt
⊢-⊨ ⊢false σ GG M' (M→*M' , —↛M') with refl ← —↛-M→*M M→*M' (λ { _ () }) = tt
```

- Case `if`

```agda
⊢-⊨ {M = if L M N} (⊢if ⊢L ⊢M ⊢N) σ GG M' (M→*M' , —↛M')
  with L' , σL→L' , –↛L' ← if—↛ M→*M' —↛M'
  with 𝒱⟦Bool⟧-Canonical (⊢-⊨ ⊢L σ GG L' (σL→L' , –↛L'))
... | inj₁ refl = ⊢-⊨ ⊢M σ GG M'
      (conf—↛join M→*M' (—→*-trans (if-cong σL→L') (_ —→⟨ β-if₁ ⟩ subst σ M ∎)) —↛M' , —↛M')
... | inj₂ refl = ⊢-⊨ ⊢N σ GG M'
      (conf—↛join M→*M' (—→*-trans (if-cong σL→L') (_ —→⟨ β-if₂ ⟩ subst σ N ∎)) —↛M' , —↛M')
```

## Semantic Type Soundness

Syntactically well typed is safe.

```agda
safety : ∀ {M A} → ∅ ⊢ M ⦂ A → Safe M
safety ⊢M = ⊨safe (⊢-⊨ ⊢M)
```
