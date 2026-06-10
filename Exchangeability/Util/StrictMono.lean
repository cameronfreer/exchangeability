/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort

/-!
# Strictly Monotone Function Utilities

Utility lemmas for strictly monotone functions on `Fin m → ℕ`, commonly used
in subsequence selection and permutation construction arguments.

## Main Results

* `strictMono_Fin_ge_id`: For strictly monotone `k : Fin m → ℕ`, values dominate indices
* `injective_implies_strictMono_perm`: Any injective `k : Fin m → ℕ` can be composed with
  a permutation to become strictly monotone

These lemmas are used extensively in exchangeability and contractability proofs
when working with strictly increasing subsequences.

## Implementation Notes

The file has no project dependencies - imports only mathlib.
All lemmas are general-purpose utilities for `Fin` and strict monotonicity.
-/

namespace Exchangeability.Util.StrictMono

variable {m n : ℕ}

/--
For a strictly monotone function `k : Fin m → ℕ`, the values dominate the indices.

**Statement:** For all `i : Fin m`, we have `i ≤ k(i)`.

**Intuition:** If you select `m` values from ℕ in strictly increasing order,
the i-th selected value must be at least i (since you've already selected i values
before it, all distinct).

**Example:** If `k = [3, 5, 7]` (selecting 3 values), then:
- `k(0) = 3 ≥ 0` ✓
- `k(1) = 5 ≥ 1` ✓
- `k(2) = 7 ≥ 2` ✓

This is crucial for proving that strictly increasing subsequences can be realized
by permutations.
-/
lemma strictMono_Fin_ge_id {k : Fin m → ℕ} (hk : StrictMono k) (i : Fin m) :
    i.val ≤ k i := by
  classical
  -- Proof by strong induction on i.val
  have : ∀ n (hn : n < m), n ≤ k ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
        intro hn
        have hn' : n < m := Nat.lt_of_succ_lt hn
        let j : Fin m := ⟨n, hn'⟩
        let j_succ : Fin m := ⟨n.succ, hn⟩
        have hlt : j < j_succ := by simp [Fin.lt_def, j, j_succ]
        have hk_lt : k j < k j_succ := hk hlt
        have ih' : n ≤ k j := ih hn'
        calc n.succ
            = n + 1 := rfl
          _ ≤ k j + 1 := Nat.add_le_add_right ih' 1
          _ ≤ k j_succ := Nat.succ_le_of_lt hk_lt
  exact this i.val i.isLt

/-- Any injective function `k : Fin m → ℕ` can be composed with a permutation
to become strictly monotone.

The permutation is `Tuple.sort k`; monotone-after-sorting plus injectivity gives
strict monotonicity.

This is a key lemma for reducing proofs about injective index selections to
proofs about strictly monotone (consecutive-like) selections via contractability.
-/
lemma injective_implies_strictMono_perm
    (k : Fin m → ℕ) (hk : Function.Injective k) :
    ∃ (σ : Equiv.Perm (Fin m)), StrictMono (fun i => k (σ i)) :=
  ⟨Tuple.sort k, (Tuple.monotone_sort k).strictMono_of_injective
    (hk.comp (Tuple.sort k).injective)⟩

end Exchangeability.Util.StrictMono
