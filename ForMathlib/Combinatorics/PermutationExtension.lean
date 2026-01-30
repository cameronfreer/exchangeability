/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic

/-!
# Extension of Injective Functions to Permutations

This file proves that injective functions from `Fin m` to `Fin n` can be extended to permutations
of `Fin n`.

## Main Results

* `Equiv.Perm.exists_extending_injective`: Any injective function `k : Fin m → Fin n` can be
  extended to a permutation `σ : Perm (Fin n)` such that `σ (Fin.castLE hmn i) = k i` for all `i`.

* `Equiv.Perm.exists_extending_strictMono`: The special case for strictly monotone functions.

## Implementation Notes

The construction uses `Equiv.extendSubtype` to extend an equivalence between subtypes to a
permutation of the ambient type. We compose:
- `(Fin.castLEquiv hmn).symm`: identifies `{x : Fin n | x.val < m}` with `Fin m`
- `Equiv.ofInjective k hk`: identifies `Fin m` with the range of `k`

Then `Equiv.extendSubtype` extends this to a full permutation.
-/

namespace Equiv.Perm

/-- Any injective function `k : Fin m → Fin n` can be extended to a permutation of `Fin n`.

The permutation agrees with `k` on the image of `Fin.castLE`: for all `i : Fin m`,
we have `σ (Fin.castLE hmn i) = k i`. -/
theorem exists_extending_injective {m n : ℕ} (k : Fin m → Fin n) (hk : Function.Injective k)
    (hmn : m ≤ n) : ∃ σ : Perm (Fin n), ∀ i : Fin m, σ (Fin.castLE hmn i) = k i :=
  let e := (Fin.castLEquiv hmn).symm.trans (Equiv.ofInjective k hk)
  ⟨e.extendSubtype, fun i => Equiv.extendSubtype_apply_of_mem e (Fin.castLE hmn i) i.isLt⟩

/-- Any strictly monotone function `k : Fin m → Fin n` can be extended to a permutation. -/
theorem exists_extending_strictMono {m n : ℕ} (k : Fin m → Fin n) (hk : StrictMono k)
    (hmn : m ≤ n) : ∃ σ : Perm (Fin n), ∀ i : Fin m, σ (Fin.castLE hmn i) = k i :=
  exists_extending_injective k hk.injective hmn

end Equiv.Perm

/-! ### Backward-compatible API

The following lemmas provide the original API using `k : Fin m → ℕ` with explicit bounds,
for use in the exchangeability project. -/

namespace Combinatorics

variable {m n : ℕ}

/-- Any injective function `k : Fin m → ℕ` with bounded range can be extended to a permutation.

Given `k : Fin m → ℕ` with `k i < n` for all `i` and `m ≤ n`, there exists `σ : Perm (Fin n)`
such that `(σ ⟨i, _⟩).val = k i` for all `i < m`. -/
theorem exists_perm_extending_injective (k : Fin m → ℕ)
    (hk_inj : Function.Injective k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m, (σ ⟨i.val, i.isLt.trans_le hmn⟩).val = k i := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_injective
    (fun i => ⟨k i, hk_bound i⟩) (fun _ _ h => hk_inj (Fin.mk.inj h)) hmn
  exact ⟨σ, fun i => congrArg Fin.val (hσ i)⟩

/-- Any strictly monotone function `k : Fin m → ℕ` with bounded range can be extended to a
permutation. -/
theorem exists_perm_extending_strictMono (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m, (σ ⟨i.val, i.isLt.trans_le hmn⟩).val = k i :=
  exists_perm_extending_injective k hk_mono.injective hk_bound hmn

end Combinatorics
