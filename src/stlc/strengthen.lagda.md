---
title: Strengthening
---

```agda
module stlc.strengthen where
```

Strengthening is the opposite of the *weakening* lemma, it basically states the following:

```txt
Γ , x : A ⊢ M : B    x ∉ fv(M)
------------------------------- (strengthen)
Γ ⊢ M : B
```

## Imports

```agda
open import stlc.base
open import stlc.subst using (extensionality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc; _≟_)
open import Data.Fin.Properties using (punchInᵢ≢i)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
```

## Anti-Rename Lemma

Instead of reasoning about a single variable, we need to reason about the *renamed* context:

```agda
ty-antirename : ∀ {m M A} {Δ : Context m}
  → Δ ⊢ M ⦂ A
  → ∀ {n N ρ} {Γ : Context n} → (∀ {x B} → Δ ∋ ρ x ⦂ B → Γ ∋ x ⦂ B)
  → M ≡ rename ρ N
    ---------------
  → Γ ⊢ N ⦂ A
ty-antirename (⊢var x)         {N = ` y}        ⊢ρ refl = ⊢var (⊢ρ x)
ty-antirename (⊢abs ⊢M)        {N = ƛ N}        ⊢ρ refl
  = ⊢abs (ty-antirename ⊢M (λ { {x = zero} Z → Z ; {x = suc x} (S ∋x) → S (⊢ρ ∋x) }) refl)
ty-antirename (⊢app ⊢M ⊢M₁)    {N = N · N₁}     ⊢ρ refl
  = ⊢app (ty-antirename ⊢M ⊢ρ refl) (ty-antirename ⊢M₁ ⊢ρ refl)
ty-antirename ⊢true            {N = true}       ⊢ρ refl = ⊢true
ty-antirename ⊢false           {N = false}      ⊢ρ refl = ⊢false
ty-antirename (⊢if ⊢M ⊢M₁ ⊢M₂) {N = if N N₁ N₂} ⊢ρ refl
  = ⊢if (ty-antirename ⊢M ⊢ρ refl) (ty-antirename ⊢M₁ ⊢ρ refl) (ty-antirename ⊢M₂ ⊢ρ refl)
```

And *strengthening* is just a special case of *anti-rename*:

```agda
ty-strengthen : ∀ {n M A B} {Γ : Context n}
  → Γ ,- B ⊢ rename suc M ⦂ A
    -------------------------
  → Γ ⊢ M ⦂ A
ty-strengthen ⊢M = ty-antirename ⊢M (λ { (S ∋x) → ∋x }) refl
```

## Occurrence Checking

While checking whether a term is shifted (renamed) can be difficult, checking the occurrence of 
a single variable in a term can be easy.

We define the predicate for checking whether a variable `x` appears in a term `M` as follows:

```agda
_∈_ : ∀ {n} → Fin n → Term n → Set
x ∈ (` y)    = x ≡ y
x ∈ (ƛ M)    = suc x ∈ M
x ∈ (M · N)  = x ∈ M ⊎ x ∈ N
x ∈ true     = ⊥
x ∈ false    = ⊥
x ∈ if L M N = x ∈ L ⊎ x ∈ M ⊎ x ∈ N
```

We show that the occurrence check is decidable:

```agda
_∈?_ : ∀ {n} → (x : Fin n) → (M : Term n) → Dec (x ∈ M)
x ∈? (` y) with x ≟ y 
... | yes x=y = yes x=y
... | no  x≠y = no x≠y
x ∈? (ƛ M) with (suc x) ∈? M
... | yes x∈M = yes x∈M
... | no x∉M  = no x∉M
x ∈? (M · N) with x ∈? M | x ∈? N
... | yes x∈M | _       = yes (inj₁ x∈M)
... | _       | yes x∈N = yes (inj₂ x∈N)
... | no x∉M  | no x∉N  = no λ { (inj₁  x∈M) → x∉M x∈M ; (inj₂  x∈N) → x∉N x∈N }
x ∈? true = no λ ()
x ∈? false = no λ ()
x ∈? if L M N with x ∈? L | x ∈? M | x ∈? N
... | yes x∈L | _       | _       = yes (inj₁ x∈L)
... | _       | yes x∈M | _       = yes (inj₂ (inj₁ x∈M))
... | _       | _       | yes x∈N = yes (inj₂ (inj₂ x∈N))
... | no x∉L  | no x∉M  | no x∉N  = no λ { (inj₁ x∈L) → x∉L x∈L ; (inj₂ (inj₁ x∈M)) → x∉M x∈M ; (inj₂ (inj₂ x∈N)) → x∉N x∈N }
```

Before proceeding to the actual lemmas, we need prove some properties of `Fin.punchIn` (shift at position `k`):

```agda
punchIn-ext : ∀ {n} {k : Fin (suc n)} → Fin.punchIn (suc k) ≡ ext (Fin.punchIn k)
punchIn-ext = extensionality lemma
  where
    lemma : ∀ {n k} (x : Fin (suc n)) → Fin.punchIn (suc k) x ≡ ext (Fin.punchIn k) x
    lemma {k = zero}  zero    = refl
    lemma {k = suc k} zero    = refl
    lemma {k = zero}  (suc x) = refl
    lemma {k = suc k} (suc x) = refl

punchIn-∃ : ∀ {n} (k x : Fin (suc n)) → k ≢ x → ∃[ y ] x ≡ Fin.punchIn k y
punchIn-∃ zero          zero          ev = ⊥-elim (ev refl)
punchIn-∃ zero          (suc x)       ev = x , refl
punchIn-∃ (suc zero)    zero          ev = zero , refl
punchIn-∃ (suc (suc k)) zero          ev = zero , refl
punchIn-∃ (suc zero)    (suc zero)    ev = ⊥-elim (ev refl)
punchIn-∃ (suc (suc k)) (suc zero)    ev with y , w ← punchIn-∃ (suc k) zero (λ z → ev (Eq.cong suc z)) = suc y , Eq.cong suc w
punchIn-∃ (suc zero)    (suc (suc x)) ev with y , w ← punchIn-∃ zero (suc x) (λ z → ev (Eq.cong suc z)) = suc y , Eq.cong suc w
punchIn-∃ (suc (suc k)) (suc (suc x)) ev with y , w ← punchIn-∃ (suc k) (suc x) (λ z → ev (Eq.cong suc z)) = suc y , Eq.cong suc w
```

Now we can show that if a variable `k` does not appear in a term `M`, is the a term shifted (renamed) at position `k`:

```agda
k∉M-N↑ : ∀ {n k} {M : Term (suc n)} → ¬ (k ∈ M) → ∃[ N ] M ≡ rename (Fin.punchIn k) N
k∉M-N↑ {k = k} {M = ` x} ev 
  with y , w ← punchIn-∃ k x ev 
  = ` y , Eq.cong `_ w
k∉M-N↑ {M = ƛ M} ev 
  with N , refl ← k∉M-N↑ {M = M} ev 
  = ƛ N , Eq.cong (λ x → ƛ rename x N) punchIn-ext
k∉M-N↑ {M = M · M₁} ev
  with N  , refl ← k∉M-N↑ {M = M} (λ z → ev (inj₁ z))
  |    N₁ , refl ← k∉M-N↑ {M = M₁} (λ z → ev (inj₂ z))
  = N · N₁ , refl
k∉M-N↑ {M = true}       ev = true , refl
k∉M-N↑ {M = false}      ev = false , refl
k∉M-N↑ {M = if M M₁ M₂} ev
  with N  , refl ← k∉M-N↑ {M = M} (λ z → ev (inj₁ z))
  |    N₁ , refl ← k∉M-N↑ {M = M₁} (λ z → ev (inj₂ (inj₁ z)))
  |    N₂ , refl ← k∉M-N↑ {M = M₂} (λ z → ev (inj₂ (inj₂ z)))
  = if N N₁ N₂ , refl
```

If a term has been shifted at position `k`, the variable does not appear in the shifted term:

```agda
N↑-k∉M : ∀ {n k N} {M : Term (suc n)} → M ≡ rename (Fin.punchIn k) N → ¬ (k ∈ M)
N↑-k∉M {N = ` x}        {M = ` y}        refl z               = punchInᵢ≢i _ _ (Eq.sym z)
N↑-k∉M {N = ƛ N}        {M = ƛ M}        refl                 = N↑-k∉M {N = N} {M = M} (Eq.cong (λ z → rename z N) (Eq.sym punchIn-ext))
N↑-k∉M {N = N · N₁}     {M = M · M₁}     refl (inj₁ x)        = N↑-k∉M {N = N} {M = M} refl x
N↑-k∉M {N = N · N₁}     {M = M · M₁}     refl (inj₂ x)        = N↑-k∉M {N = N₁} {M = M₁} refl x
N↑-k∉M {N = true}       {M = true}       refl ()
N↑-k∉M {N = false}      {M = false}      refl ()
N↑-k∉M {N = if N N₁ N₂} {M = if M M₁ M₂} refl (inj₁ x)        = N↑-k∉M {N = N} {M = M} refl x
N↑-k∉M {N = if N N₁ N₂} {M = if M M₁ M₂} refl (inj₂ (inj₁ x)) = N↑-k∉M {N = N₁} {M = M₁} refl x
N↑-k∉M {N = if N N₁ N₂} {M = if M M₁ M₂} refl (inj₂ (inj₂ x)) = N↑-k∉M {N = N₂} {M = M₂} refl x
```
