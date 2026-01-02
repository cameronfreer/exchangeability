/-
Copyright (c) 2025 The Exchangeability Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Exchangeability.PathSpace.Shift
import Exchangeability.Ergodic.ShiftInvariantSigma

/-!
# Block Injection for Disjoint-Block Averaging

This file defines the **block injection** map used in the disjoint-block averaging argument
for de Finetti's theorem via contractability. The block injection allows us to select one
element from each of m disjoint blocks, while preserving strict monotonicity (required for
contractability).

## Main definitions

* `blockInjection m n j`: For `j : Fin m → Fin n`, maps:
  - `i < m` to `i * n + j(i)` (selects element j(i) from block i)
  - `i ≥ m` to `i + (m * n - m)` (shifts the tail)

## Main results

* `blockInjection_strictMono`: The block injection is strictly monotone when n > 0.
* `blockInjectionEmb`: Embedding version of block injection.

## Mathematical context

The disjoint-block averaging argument (Kallenberg's "first proof") works as follows:
1. Partition `ℕ` into m blocks of size n each: `[0, n), [n, 2n), ..., [(m-1)n, mn)`
2. For each choice function `j : Fin m → Fin n`, the block injection selects one element
   from each block while being strictly monotone
3. Average over all n^m such choices to get block averages
4. As n → ∞, block averages converge to conditional expectations

This approach avoids permutations entirely, using only strictly monotone injections,
which is exactly what contractability requires.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

namespace Exchangeability.DeFinetti

open Exchangeability.PathSpace

variable {α : Type*} [MeasurableSpace α]

/-! ### Block Injection Definition -/

/-- Block injection: for `i < m`, select element `j(i)` from block `i`;
for `i ≥ m`, shift by `m * n - m` to avoid collision.

The result is strictly monotone when `n > 0`, making it suitable for
contractability arguments. -/
def blockInjection (m n : ℕ) (j : Fin m → Fin n) : ℕ → ℕ :=
  fun i => if h : i < m then i * n + (j ⟨i, h⟩).val else i + (m * n - m)

@[simp]
lemma blockInjection_apply_lt {m n : ℕ} {j : Fin m → Fin n} {i : ℕ} (hi : i < m) :
    blockInjection m n j i = i * n + (j ⟨i, hi⟩).val := by
  simp [blockInjection, hi]

@[simp]
lemma blockInjection_apply_ge {m n : ℕ} {j : Fin m → Fin n} {i : ℕ} (hi : m ≤ i) :
    blockInjection m n j i = i + (m * n - m) := by
  simp [blockInjection, not_lt.mpr hi]

/-! ### Strict Monotonicity -/

/-- Block injection is strictly monotone when block size n > 0. -/
lemma blockInjection_strictMono (m n : ℕ) (hn : 0 < n) (j : Fin m → Fin n) :
    StrictMono (blockInjection m n j) := by
  intro i i' hii'
  -- Case split based on whether i, i' are in the first m indices
  by_cases hi : i < m
  · by_cases hi' : i' < m
    · -- Case 1: i < i' < m
      -- ρ(i) = i*n + j(i) and ρ(i') = i'*n + j(i')
      -- Need: i*n + j(i) < i'*n + j(i')
      simp only [blockInjection_apply_lt hi, blockInjection_apply_lt hi']
      -- Since i < i' and both < m, we have i + 1 ≤ i'
      -- So i*n + j(i) < (i+1)*n ≤ i'*n ≤ i'*n + j(i')
      have h1 : i * n + (j ⟨i, hi⟩).val < (i + 1) * n := by
        have hj_bound : (j ⟨i, hi⟩).val < n := (j ⟨i, hi⟩).isLt
        calc i * n + (j ⟨i, hi⟩).val
          _ < i * n + n := Nat.add_lt_add_left hj_bound _
          _ = (i + 1) * n := by ring
      have h2 : (i + 1) * n ≤ i' * n := by
        have : i + 1 ≤ i' := hii'
        exact Nat.mul_le_mul_right n this
      omega
    · -- Case 2: i < m ≤ i'
      -- ρ(i) = i*n + j(i) and ρ(i') = i' + (m*n - m)
      simp only [blockInjection_apply_lt hi, blockInjection_apply_ge (Nat.le_of_not_lt hi')]
      -- ρ(i) < m*n ≤ ρ(i')
      have h1 : i * n + (j ⟨i, hi⟩).val < m * n := by
        have hj_bound : (j ⟨i, hi⟩).val < n := (j ⟨i, hi⟩).isLt
        have hi_bound : i + 1 ≤ m := hi
        calc i * n + (j ⟨i, hi⟩).val
          _ < i * n + n := by omega
          _ = (i + 1) * n := by ring
          _ ≤ m * n := Nat.mul_le_mul_right n hi_bound
      have h2 : m * n ≤ i' + (m * n - m) := by
        have hm_le_i' : m ≤ i' := Nat.le_of_not_lt hi'
        -- Rewrite to avoid subtraction issues
        -- i' + (m * n - m) ≥ m + (m * n - m) = m * n
        have hmn_sub : m * n - m + m = m * n := Nat.sub_add_cancel (Nat.le_mul_of_pos_right m hn)
        calc m * n
          _ = m * n - m + m := hmn_sub.symm
          _ ≤ m * n - m + i' := by omega
          _ = i' + (m * n - m) := by ring
      omega
  · -- Case 3: m ≤ i < i'
    -- Both are in the tail, so ρ preserves order
    have hi' : m ≤ i' := Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_of_not_lt hi) hii')
    simp only [blockInjection_apply_ge (Nat.le_of_not_lt hi), blockInjection_apply_ge hi']
    omega

/-- Block injection is an embedding (strictly monotone implies injective). -/
def blockInjectionEmb (m n : ℕ) (hn : 0 < n) (j : Fin m → Fin n) : ℕ ↪ ℕ :=
  ⟨blockInjection m n j, (blockInjection_strictMono m n hn j).injective⟩

/-! ### Reindexing by Block Injection -/

/-- Reindex a sequence by block injection.

Given `ω : ℕ → α`, `j : Fin m → Fin n`, produces the sequence
where position `i` has value `ω (blockInjection m n j i)`. -/
def reindexBlock (m n : ℕ) (j : Fin m → Fin n) (ω : ℕ → α) : ℕ → α :=
  fun i => ω (blockInjection m n j i)

omit [MeasurableSpace α] in
@[simp]
lemma reindexBlock_apply (m n : ℕ) (j : Fin m → Fin n) (ω : ℕ → α) (i : ℕ) :
    reindexBlock m n j ω i = ω (blockInjection m n j i) := rfl

/-- Reindexing by block injection is measurable. -/
lemma measurable_reindexBlock (m n : ℕ) (j : Fin m → Fin n) :
    Measurable (reindexBlock (α := α) m n j) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (blockInjection m n j i)

/-! ### Block Injection Properties for First m Coordinates -/

/-- The first m values under block injection hit positions in disjoint blocks. -/
lemma blockInjection_val_lt (m n : ℕ) (j : Fin m → Fin n) (i : Fin m) :
    blockInjection m n j i.val = i.val * n + (j i).val := by
  simp [blockInjection, i.isLt]

/-- Block injection at position k yields a value in block k. -/
lemma blockInjection_mem_block (m n : ℕ) (j : Fin m → Fin n) (k : Fin m) :
    blockInjection m n j k.val ∈ Set.Ico (k.val * n) ((k.val + 1) * n) := by
  simp only [blockInjection_val_lt, Set.mem_Ico]
  constructor
  · omega
  · have hj : (j k).val < n := (j k).isLt
    calc k.val * n + (j k).val
      _ < k.val * n + n := by omega
      _ = (k.val + 1) * n := by ring

/-- Block injection values for different k are in different blocks (hence disjoint). -/
lemma blockInjection_disjoint_blocks (m n : ℕ) (j : Fin m → Fin n)
    (k₁ k₂ : Fin m) (hk : k₁ ≠ k₂) :
    blockInjection m n j k₁.val ≠ blockInjection m n j k₂.val := by
  intro h
  simp only [blockInjection_val_lt] at h
  -- If k₁ * n + j(k₁) = k₂ * n + j(k₂) and both j values < n, then k₁ = k₂
  have hj1 : (j k₁).val < n := (j k₁).isLt
  have hj2 : (j k₂).val < n := (j k₂).isLt
  -- Use Nat.div_mod uniqueness: k₁ = k₂ iff they're in the same block
  have heq_div : k₁.val * n + (j k₁).val = k₂.val * n + (j k₂).val := h
  -- WLOG: case split on k₁ < k₂ or k₂ < k₁
  rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heq | hgt
  · -- k₁ < k₂: then k₁ * n + j(k₁) < (k₁ + 1) * n ≤ k₂ * n ≤ k₂ * n + j(k₂)
    have h1 : k₁.val * n + (j k₁).val < (k₁.val + 1) * n := by
      calc k₁.val * n + (j k₁).val < k₁.val * n + n := by omega
        _ = (k₁.val + 1) * n := by ring
    have h2 : (k₁.val + 1) * n ≤ k₂.val * n := Nat.mul_le_mul_right n hlt
    have h3 : k₂.val * n ≤ k₂.val * n + (j k₂).val := Nat.le_add_right _ _
    have : k₁.val * n + (j k₁).val < k₂.val * n + (j k₂).val := calc
      k₁.val * n + (j k₁).val < (k₁.val + 1) * n := h1
      _ ≤ k₂.val * n := h2
      _ ≤ k₂.val * n + (j k₂).val := h3
    omega
  · -- k₁ = k₂: contradiction with hk
    exact hk (Fin.ext heq)
  · -- k₂ < k₁: symmetric case
    have h1 : k₂.val * n + (j k₂).val < (k₂.val + 1) * n := by
      calc k₂.val * n + (j k₂).val < k₂.val * n + n := by omega
        _ = (k₂.val + 1) * n := by ring
    have h2 : (k₂.val + 1) * n ≤ k₁.val * n := Nat.mul_le_mul_right n hgt
    have h3 : k₁.val * n ≤ k₁.val * n + (j k₁).val := Nat.le_add_right _ _
    have : k₂.val * n + (j k₂).val < k₁.val * n + (j k₁).val := calc
      k₂.val * n + (j k₂).val < (k₂.val + 1) * n := h1
      _ ≤ k₁.val * n := h2
      _ ≤ k₁.val * n + (j k₁).val := h3
    omega

/-! ### Shift-Invariance of Reindexing

For mSI-sets, reindexing by blockInjection preserves membership because:
1. For i ≥ m: blockInjection(i) = i + (m*n - m) (constant shift)
2. mSI-sets are determined by the tail (coordinates ≥ any M)
3. Therefore membership is preserved -/

omit [MeasurableSpace α] in
/-- Helper: shift^[k] ω at position n equals ω at position n + k. -/
private lemma shift_iterate_apply' (k n : ℕ) (ω : Ω[α]) :
    (shift^[k] ω) n = ω (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', shift_apply, ih]
    ring_nf

omit [MeasurableSpace α] in
/-- Helper: shift^[C] preimage of shift-invariant set is the set itself. -/
private lemma shift_iterate_preimage_of_shiftInvariant (C : ℕ) (s : Set (Ω[α]))
    (hs_shift : shift ⁻¹' s = s) :
    shift^[C] ⁻¹' s = s := by
  induction C with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ', Set.preimage_comp, hs_shift, ih]

/-- Reindexing by blockInjection preserves membership in shift-invariant sets.

The key insight is that blockInjection is eventually a constant shift:
for i ≥ m, blockInjection(i) = i + (m*n - m).

For shift-invariant sets s (where shift⁻¹(s) = s), membership is determined by
the eventual behavior of the sequence. Since blockInjection only permutes
finitely many coordinates and then shifts, it preserves membership in s. -/
lemma reindex_blockInjection_preimage_shiftInvariant {m n : ℕ} (hn : 0 < n)
    (j : Fin m → Fin n) (s : Set (Ω[α]))
    (hs : isShiftInvariant s) :
    (fun ω => ω ∘ blockInjection m n j) ⁻¹' s = s := by
  -- hs gives: MeasurableSet s and shift ⁻¹' s = s
  obtain ⟨hs_meas, hs_shift⟩ := hs
  ext ω
  simp only [Set.mem_preimage]
  -- Need: ω ∈ s ↔ (ω ∘ blockInjection m n j) ∈ s
  --
  -- Key observation: for i ≥ m, blockInjection(i) = i + (m*n - m)
  -- So (ω ∘ blockInjection) agrees with shift^{m*n-m}(ω) on coordinates ≥ m.
  -- By shift-invariance, ω ∈ s iff shift^{m*n-m}(ω) ∈ s.
  -- By "tail property" of shift-invariant sets, agreeing on coordinates ≥ m suffices.
  --
  -- Let C = m * n - m (the shift amount for i ≥ m).
  let C := m * n - m
  -- Let ρ = blockInjection m n j
  let ρ := blockInjection m n j
  -- For i ≥ m: ρ(i) = i + C
  have h_tail : ∀ i, m ≤ i → ρ i = i + C := fun i hi => blockInjection_apply_ge hi
  -- By shift-invariance: ω ∈ s iff shift^C(ω) ∈ s
  have h_shift_C : shift^[C] ⁻¹' s = s := shift_iterate_preimage_of_shiftInvariant C s hs_shift
  have h_shift_iff : ω ∈ s ↔ shift^[C] ω ∈ s := by
    rw [← Set.mem_preimage, h_shift_C]
  -- By tail property: shift^C(ω) ∈ s iff (ω ∘ ρ) ∈ s
  -- For this, we use that membership in shift-invariant sets is determined by
  -- coordinates ≥ m (via applying shift^m and using shift-invariance).
  --
  -- Specifically: if two sequences agree on coordinates ≥ M, then applying shift^M
  -- to both gives the same sequence starting from coordinate 0.
  have h_tail_prop : shift^[C] ω ∈ s ↔ (ω ∘ ρ) ∈ s := by
    -- Both shift^C(ω) and (ω ∘ ρ) when shifted by m give sequences that
    -- eventually agree (in fact, agree everywhere starting from some point).
    --
    -- More directly: shift^m(shift^C(ω)) and shift^m(ω ∘ ρ) are the same sequence.
    -- shift^m(shift^C(ω)) = shift^{m+C}(ω) has coordinate i equal to ω(i + m + C).
    -- shift^m(ω ∘ ρ) has coordinate i equal to (ω ∘ ρ)(i + m) = ω(ρ(i + m)).
    -- For i + m ≥ m (always true), ρ(i + m) = (i + m) + C = i + m + C.
    -- So these are equal!
    have h_shift_m_eq : shift^[m] (shift^[C] ω) = shift^[m] (ω ∘ ρ) := by
      ext i
      simp only [shift_iterate_apply', Function.comp_apply]
      rw [h_tail (i + m) (Nat.le_add_left m i)]
    -- By shift-invariance: x ∈ s iff shift^m(x) ∈ s
    have h_shift_m_inv : shift^[m] ⁻¹' s = s := shift_iterate_preimage_of_shiftInvariant m s hs_shift
    -- shift^C(ω) ∈ s iff shift^m(shift^C(ω)) ∈ s (by shift-invariance)
    -- (ω ∘ ρ) ∈ s iff shift^m(ω ∘ ρ) ∈ s (by shift-invariance)
    -- shift^m(shift^C(ω)) = shift^m(ω ∘ ρ) (proved above)
    -- Therefore: shift^C(ω) ∈ s iff (ω ∘ ρ) ∈ s
    constructor
    · intro h
      -- h : shift^[C] ω ∈ s
      -- We want: ω ∘ ρ ∈ s
      -- By h_shift_m_inv: shift^[m] (shift^[C] ω) ∈ s
      have h1 : shift^[m] (shift^[C] ω) ∈ s := by
        rw [← Set.mem_preimage, h_shift_m_inv]; exact h
      -- By h_shift_m_eq: shift^[m] (ω ∘ ρ) ∈ s
      have h2 : shift^[m] (ω ∘ ρ) ∈ s := h_shift_m_eq ▸ h1
      -- By h_shift_m_inv: ω ∘ ρ ∈ s
      rw [← Set.mem_preimage, h_shift_m_inv] at h2
      exact h2
    · intro h
      -- h : ω ∘ ρ ∈ s
      -- We want: shift^[C] ω ∈ s
      -- By h_shift_m_inv: shift^[m] (ω ∘ ρ) ∈ s
      have h1 : shift^[m] (ω ∘ ρ) ∈ s := by
        rw [← Set.mem_preimage, h_shift_m_inv]; exact h
      -- By h_shift_m_eq.symm: shift^[m] (shift^[C] ω) ∈ s
      have h2 : shift^[m] (shift^[C] ω) ∈ s := h_shift_m_eq.symm ▸ h1
      -- By h_shift_m_inv: shift^[C] ω ∈ s
      rw [← Set.mem_preimage, h_shift_m_inv] at h2
      exact h2
  -- Combine: ω ∈ s ↔ shift^C(ω) ∈ s ↔ (ω ∘ ρ) ∈ s
  rw [h_shift_iff, h_tail_prop]

end Exchangeability.DeFinetti
