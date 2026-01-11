/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort

/-!
# Strictly Monotone Function Utilities

Utility lemmas for strictly monotone functions on `Fin m → ℕ`, commonly used
in subsequence selection and permutation construction arguments.

## Main Results

* `strictMono_Fin_ge_id`: For strictly monotone `k : Fin m → ℕ`, values dominate indices
* `strictMono_add_left`, `strictMono_add_right`: Addition preserves strict monotonicity
* `fin_val_strictMono`: The identity `Fin n → ℕ` is strictly monotone
* `strictMono_comp`: Composition of strictly monotone functions
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
        have hlt : j < j_succ := by simp [Fin.lt_def, j, j_succ]
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

/-- Any injective function `k : Fin m → ℕ` can be composed with a permutation
to become strictly monotone.

**Construction:** Let `s := image k univ` (the image of k as a finset of ℕ).
Since k is injective, `s.card = m`. The `orderIsoOfFin` gives the sorted
enumeration of s. We define σ to map i to the position of k(i) in the sorted order.

**Key property:** `(fun i => k (σ i))` is strictly increasing (sorted order).

This is a key lemma for reducing proofs about injective index selections to
proofs about strictly monotone (consecutive-like) selections via contractability.
-/
lemma injective_implies_strictMono_perm
    (k : Fin m → ℕ) (hk : Function.Injective k) :
    ∃ (σ : Equiv.Perm (Fin m)), StrictMono (fun i => k (σ i)) := by
  classical
  -- Define the image of k as a finset
  let s : Finset ℕ := Finset.image k Finset.univ
  -- By injectivity, s has cardinality m
  have hs : s.card = m := by
    simp only [s, Finset.card_image_of_injective Finset.univ hk, Finset.card_univ, Fintype.card_fin]
  -- Get the sorted enumeration of s
  let sorted : Fin m ≃o ↑s := Finset.orderIsoOfFin s hs
  -- For each i : Fin m, k(i) is in s, so we can find its sorted position
  have hk_mem : ∀ i : Fin m, k i ∈ s := by
    intro i
    simp only [s, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  -- Define σ: for each position j in sorted order, find which i : Fin m maps to it
  -- sorted j gives the j-th smallest element of s
  -- We want σ such that k (σ j) = sorted j
  -- Define σ⁻¹ first: σ⁻¹(i) = sorted position of k(i)
  let σ_inv : Fin m → Fin m := fun i =>
    sorted.symm ⟨k i, hk_mem i⟩
  -- σ_inv is injective because sorted.symm and k are both injective
  have hσ_inv_inj : Function.Injective σ_inv := by
    intro i j hij
    simp only [σ_inv] at hij
    have h := sorted.symm.injective hij
    simp only [Subtype.mk.injEq] at h
    exact hk h
  -- Since σ_inv : Fin m → Fin m is injective, it's a bijection
  have hσ_inv_bij : Function.Bijective σ_inv := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hσ_inv_inj, rfl⟩
  -- Convert to an Equiv.Perm
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective σ_inv hσ_inv_bij
  -- Now σ.symm is the permutation we want
  use σ.symm
  -- Show k ∘ σ.symm is strictly monotone
  intro i j hij
  -- σ.symm(i) is the unique index such that σ_inv(σ.symm(i)) = i
  -- i.e., sorted position of k(σ.symm(i)) is i
  -- So k(σ.symm(i)) = sorted(i) (the i-th smallest element)
  have h_eq_i : k (σ.symm i) = ↑(sorted i) := by
    have h1 : σ_inv (σ.symm i) = i := by
      simp only [σ, Equiv.ofBijective_apply_symm_apply]
    simp only [σ_inv] at h1
    have h2 : sorted.symm ⟨k (σ.symm i), hk_mem (σ.symm i)⟩ = i := h1
    have h3 := sorted.apply_symm_apply ⟨k (σ.symm i), hk_mem (σ.symm i)⟩
    rw [h2] at h3
    exact Subtype.ext_iff.mp h3.symm
  have h_eq_j : k (σ.symm j) = ↑(sorted j) := by
    have h1 : σ_inv (σ.symm j) = j := by
      simp only [σ, Equiv.ofBijective_apply_symm_apply]
    simp only [σ_inv] at h1
    have h2 : sorted.symm ⟨k (σ.symm j), hk_mem (σ.symm j)⟩ = j := h1
    have h3 := sorted.apply_symm_apply ⟨k (σ.symm j), hk_mem (σ.symm j)⟩
    rw [h2] at h3
    exact Subtype.ext_iff.mp h3.symm
  -- Goal: (fun i => k (σ.symm i)) i < (fun i => k (σ.symm i)) j
  -- This simplifies to: k (σ.symm i) < k (σ.symm j)
  simp only
  rw [h_eq_i, h_eq_j]
  -- sorted is an OrderIso, so it's strictly monotone
  exact sorted.strictMono hij

end Exchangeability.Util.StrictMono
