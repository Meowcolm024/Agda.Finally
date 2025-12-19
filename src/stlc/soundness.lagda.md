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

> TODO

## Auxiliary Lemmas

> TODO

## Adequacy

> TODO

## Fundamental Property

> TODO

## Semantic Type Soundness

> TODO