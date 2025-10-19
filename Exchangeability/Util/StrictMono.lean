/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Strictly Monotone Function Utilities

Utility lemmas for strictly monotone functions on `Fin m → ℕ`, commonly used
in subsequence selection and permutation construction arguments.

## Main Results

* `strictMono_Fin_ge_id`: For strictly monotone `k : Fin m → ℕ`, values dominate indices
* `strictMono_add_left`, `strictMono_add_right`: Addition preserves strict monotonicity
* `fin_val_strictMono`: The identity `Fin n → ℕ` is strictly monotone
* `strictMono_comp`: Composition of strictly monotone functions

These lemmas are used extensively in exchangeability and contractability proofs
when working with strictly increasing subsequences.

## Implementation Notes

The file has no project dependencies - imports only mathlib.
All lemmas are general-purpose utilities for `Fin` and strict monotonicity.
-/

namespace Exchangeability.Util.StrictMono

variable {m n : ℕ}

/-- Composing strictly monotone functions with left addition preserves strict monotonicity.

For any strictly monotone `k : Fin m → ℕ` and constant `c`, the function
`i ↦ c + k(i)` is also strictly monotone. -/
lemma strictMono_add_left (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => c + k i) :=
  fun ⦃_ _⦄ hab ↦ Nat.add_lt_add_left (hk hab) c

/-- Composing strictly monotone functions with right addition preserves strict monotonicity.

For any strictly monotone `k : Fin m → ℕ` and constant `c`, the function
`i ↦ k(i) + c` is also strictly monotone. -/
lemma strictMono_add_right (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => k i + c) :=
  fun ⦃_ _⦄ hab ↦ Nat.add_lt_add_right (hk hab) c

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
        have hlt : j < j_succ := by
          simp only [Fin.lt_iff_val_lt_val, j, j_succ]
          exact Nat.lt_succ_self n
        have hk_lt : k j < k j_succ := hk hlt
        have ih' : n ≤ k j := ih hn'
        calc n.succ
            = n + 1 := rfl
          _ ≤ k j + 1 := Nat.add_le_add_right ih' 1
          _ ≤ k j_succ := Nat.succ_le_of_lt hk_lt
  exact this i.val i.isLt

/--
The identity function `Fin n → ℕ` is strictly monotone.

The canonical embedding of `Fin n` into `ℕ` preserves the order structure.
-/
lemma fin_val_strictMono : StrictMono (fun i : Fin n => i.val) := by
  intro i j hij
  exact hij

/--
Composing strictly monotone functions preserves strict monotonicity.

If `f : Fin m → Fin n` is strictly monotone and `g : Fin n → ℕ` is strictly
monotone, then their composition `g ∘ f` is strictly monotone.
-/
lemma strictMono_comp (f : Fin m → Fin n) (g : Fin n → ℕ)
    (hf : StrictMono f) (hg : StrictMono g) : StrictMono (fun i => g (f i)) :=
  fun ⦃_ _⦄ hab ↦ hg (hf hab)

end Exchangeability.Util.StrictMono
