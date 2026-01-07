/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.Probability.MeasureKernels

/-!
# Finite Cylinder Machinery for Kallenberg Lemma 1.3

This file provides the finite approximation infrastructure for proving
conditional independence from contractability.

## Main definitions

* `finFutureSigma X m k` - Finite approximation of the future σ-algebra
* `contractable_finite_cylinder_measure` - Cylinder measure formula from contractability
* `contractable_triple_pushforward` - Triple pushforward equality
* `join_eq_comap_pair_finFuture` - σ-algebra join characterization

## Strategy

We prove conditional independence by working with finite future approximations.
The key insight is that contractability implies distributional equality for
cylinder sets, which extends to the full σ-algebra via π-λ theorem.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open MartingaleHelpers

/-! ### Finite Future σ-Algebra -/

/-- **Finite future σ-algebra.**

Approximates the infinite future σ(X_{m+1}, X_{m+2}, ...) by finite truncation. -/
def finFutureSigma (X : ℕ → Ω → α) (m k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) inferInstance

lemma finFutureSigma_le_ambient
    (X : ℕ → Ω → α) (m k : ℕ) (hX : ∀ n, Measurable (X n)) :
    finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have : Measurable (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) := by measurability
  exact this ht

omit [MeasurableSpace Ω] in
lemma finFutureSigma_le_futureFiltration
    (X : ℕ → Ω → α) (m k : ℕ) :
    finFutureSigma X m k ≤ futureFiltration X m := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  -- s = (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) ⁻¹' t
  -- Need to show this is in futureFiltration X m

  -- The finite projection factors through the infinite one:
  -- (fun ω => fun i => X (m + 1 + i.val) ω) = proj ∘ (shiftRV X (m+1))
  -- where proj : (ℕ → α) → (Fin k → α) takes first k coordinates

  let proj : (ℕ → α) → (Fin k → α) := fun f i => f i.val

  have h_factor : (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) = proj ∘ (shiftRV X (m + 1)) := by
    ext ω i
    simp only [Function.comp_apply, proj, shiftRV]

  -- Since proj is measurable, proj ⁻¹' t is measurable in (ℕ → α)
  have h_proj_meas : Measurable proj := by measurability
  have h_proj_t_meas : MeasurableSet (proj ⁻¹' t) := h_proj_meas ht

  -- Provide witness for comap: s ∈ futureFiltration means ∃ t', s = (shiftRV X (m+1)) ⁻¹' t'
  refine ⟨proj ⁻¹' t, h_proj_t_meas, ?_⟩

  -- Show s = (shiftRV X (m+1)) ⁻¹' (proj ⁻¹' t)
  rw [← Set.preimage_comp, ← h_factor]

/-! ### Cylinder Set Measure Formula -/

/-- **Cylinder set measure formula from contractability (finite approximation).**

For contractable sequences with r < m, the measure of joint cylinder events involving
the first r coordinates, coordinate r, and k future coordinates can be expressed using
contractability properties.

This provides the distributional foundation for proving conditional independence in the
finite approximation setting. -/
lemma contractable_finite_cylinder_measure
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m k : ℕ} (hrm : r < m)
    (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    -- The joint measure equals the measure for the standard cylinder
    μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)})
      = μ ({ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)}) := by
  -- Strategy: The indices (0,...,r-1, r, m+1,...,m+k) form a strictly increasing sequence.
  -- By contractability, this has the same distribution as (0,...,r-1, r, r+1,...,r+k).

  -- Define the index function: Fin (r + 1 + k) → ℕ
  -- Maps i to: i if i ≤ r, and m + i - r if i > r
  let idx : Fin (r + 1 + k) → ℕ := fun i =>
    if h : i.val < r + 1 then i.val else m + 1 + (i.val - r - 1)

  -- Show idx is strictly monotone
  have idx_mono : StrictMono idx := by
    intro i j hij
    simp only [idx]
    split_ifs with hi hj hj
    · -- Both i, j ≤ r: use i < j directly
      exact hij
    · -- i ≤ r < j: show i < m + 1 + (j - r - 1)
      have : j.val ≥ r + 1 := Nat.le_of_not_lt hj
      calc i.val
        _ < r + 1 := hi
        _ ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hrm) 1
        _ ≤ m + 1 + (j.val - r - 1) := Nat.le_add_right _ _
    · -- i ≤ r but not j < r + 1: contradiction
      omega
    · -- Both i, j > r: use the fact that j.val - r - 1 > i.val - r - 1
      have hi' : i.val ≥ r + 1 := Nat.le_of_not_lt hi
      have hj' : j.val ≥ r + 1 := Nat.le_of_not_lt hj
      calc m + 1 + (i.val - r - 1)
        _ < m + 1 + (j.val - r - 1) := Nat.add_lt_add_left (Nat.sub_lt_sub_right hi' hij) _

  -- Apply contractability: subsequence via idx has same distribution as 0,...,r+k
  have contract := hX (r + 1 + k) idx idx_mono

  -- Define the product set corresponding to our cylinder conditions
  let S : Set (Fin (r + 1 + k) → α) :=
    {f | (∀ i : Fin r, f ⟨i.val, by omega⟩ ∈ A i) ∧ f ⟨r, by omega⟩ ∈ B ∧
         (∀ j : Fin k, f ⟨r + 1 + j.val, by omega⟩ ∈ C j)}

  -- Key: Show that the LHS and RHS sets are preimages under the respective mappings

  -- The LHS: {ω | X_0,...,X_{r-1} ∈ A, X_r ∈ B, X_{m+1},...,X_{m+k} ∈ C}
  -- is exactly the preimage of S under (fun ω i => X (idx i) ω)
  have lhs_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      = (fun ω => fun i => X (idx i) ω) ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S]
    constructor
    · intro ⟨hA, hB, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        -- For i < r: idx(i) = i, so X(idx i) ω = X i ω ∈ A i
        have hi : idx ⟨i.val, by omega⟩ = i.val := by
          simp only [idx]; split_ifs <;> omega
        rw [hi]
        exact hA i
      · -- For i = r: idx(r) = r, so X(idx r) ω = X r ω ∈ B
        have : idx ⟨r, by omega⟩ = r := by
          simp only [idx]; split_ifs <;> omega
        rw [this]
        exact hB
      · intro j
        -- For i = r+1+j: idx(r+1+j) = m+1+j
        have : idx ⟨r + 1 + j.val, by omega⟩ = m + 1 + j.val := by
          simp only [idx]
          split_ifs with h
          · omega
          · have : r + 1 + j.val - r - 1 = j.val := by omega
            rw [this]
        rw [this]
        exact hC j
    · intro ⟨hA, hB, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have : idx ⟨i.val, by omega⟩ = i.val := by
          simp only [idx]; split_ifs <;> omega
        rw [← this]
        exact hA ⟨i.val, by omega⟩
      · have : idx ⟨r, by omega⟩ = r := by
          simp only [idx]; split_ifs <;> omega
        rw [← this]
        exact hB
      · intro j
        have idx_val : idx ⟨r + 1 + j.val, by omega⟩ = m + 1 + j.val := by
          simp only [idx]
          split_ifs with h
          · omega
          · have : r + 1 + j.val - r - 1 = j.val := by omega
            rw [this]
        rw [← idx_val]
        exact hC j

  -- The RHS is the preimage of S under (fun ω i => X i.val ω)
  have rhs_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (r + 1 + j.val) ω ∈ C j)}
      = (fun ω => fun i => X i.val ω) ⁻¹' S := by
    ext ω; simp [S]

  -- Apply contractability: the pushforward measures are equal
  rw [lhs_eq, rhs_eq]

  -- contract says the two pushforward measures are equal:
  -- Measure.map (fun ω i => X (idx i) ω) μ = Measure.map (fun ω i => X i.val ω) μ
  --
  -- Goal is: μ ((fun ω i => X (idx i) ω) ⁻¹' S) = μ ((fun ω i => X i.val ω) ⁻¹' S)
  --
  -- Since the measures are equal, they assign equal measure to preimages

  -- First prove S is measurable
  have hS_meas : MeasurableSet S := by
    -- Use intersection decomposition approach
    -- S = (⋂ i : Fin r, preimage at i) ∩ (preimage at r) ∩ (⋂ j : Fin k, preimage at r+1+j)
    have h_decomp : S =
        (⋂ i : Fin r, {f | f ⟨i.val, by omega⟩ ∈ A i}) ∩
        {f | f ⟨r, by omega⟩ ∈ B} ∩
        (⋂ j : Fin k, {f | f ⟨r + 1 + j.val, by omega⟩ ∈ C j}) := by
      ext f; simp only [S, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf]; tauto

    rw [h_decomp]
    exact .inter (.inter (.iInter fun i => measurable_pi_apply (Fin.mk i.val (by omega)) (hA i))
      (measurable_pi_apply (Fin.mk r (by omega)) hB))
      (.iInter fun j => measurable_pi_apply (Fin.mk (r + 1 + j.val) (by omega)) (hC j))

  -- Apply measure equality (with inline measurability from fun_prop)
  calc μ ((fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) ⁻¹' S)
      = Measure.map (fun ω i => X (idx i) ω) μ S := by
        rw [Measure.map_apply (by fun_prop (disch := measurability)) hS_meas]
    _ = Measure.map (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) μ S := by rw [contract]
    _ = μ ((fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) ⁻¹' S) := by
        rw [Measure.map_apply (by fun_prop (disch := measurability)) hS_meas]

/-! ### Triple Pushforward -/

/-- Contractability implies equality of the joint law of
`(X₀,…,X_{r-1}, X_r, X_{m+1}, …, X_{m+k})` and
`(X₀,…,X_{r-1}, X_r, X_{r+1}, …, X_{r+k})`. -/
lemma contractable_triple_pushforward
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m k : ℕ} (hrm : r < m) :
  let Z_r : Ω → (Fin r → α) := fun ω i => X i.val ω
  let Y_future : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.val) ω
  let Y_tail   : Ω → (Fin k → α) := fun ω j => X (r + 1 + j.val) ω
  Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ
    = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ := by
  classical
  intro Z_r Y_future Y_tail
  -- Use triple rectangles from MeasureKernels.lean
  let Rectangles := TripleRectangles r k α

  -- Rectangles form a π-system (from MeasureKernels.lean)
  have h_pi : IsPiSystem Rectangles := tripleRectangles_isPiSystem

  -- Equality on rectangles using the finite cylinder measure lemma.
  have h_agree :
      ∀ {S} (hS : S ∈ Rectangles),
        Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ S
          = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ S := by
    intro S hS
    rcases hS with ⟨A, hA, B, hB, C, hC, rfl⟩
    -- Convert preimage of rectangle into the cylinder event.
    have h_pre_future :
        (fun ω => (Z_r ω, X r ω, Y_future ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_future, Set.mem_setOf_eq]
    have h_pre_tail :
        (fun ω => (Z_r ω, X r ω, Y_tail ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_tail, Set.mem_setOf_eq]
    -- Apply the finite cylinder equality.
    have h_cyl :=
      contractable_finite_cylinder_measure
        (X := X) (μ := μ) (hX := hX) (hX_meas := hX_meas)
        (hrm := hrm) (A := A) (hA := hA) (B := B) (hB := hB)
        (C := C) (hC := hC)
    -- Convert to map equality
    -- First, prove measurability of the triple functions
    have h_meas_future : Measurable (fun ω => (Z_r ω, X r ω, Y_future ω)) := by
      refine Measurable.prodMk ?_ (Measurable.prodMk (hX_meas r) ?_)
      · measurability
      · measurability
    have h_meas_tail : Measurable (fun ω => (Z_r ω, X r ω, Y_tail ω)) := by
      refine Measurable.prodMk ?_ (Measurable.prodMk (hX_meas r) ?_)
      · measurability
      · measurability
    -- The rectangle is measurable
    have h_meas_rect : MeasurableSet ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)) := by
      show MeasurableSet ((Set.univ.pi A) ×ˢ (B ×ˢ (Set.univ.pi C)))
      exact (MeasurableSet.univ_pi hA).prod (hB.prod (MeasurableSet.univ_pi hC))
    -- Apply Measure.map_apply and rewrite using preimage equalities
    calc Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
        = μ ((fun ω => (Z_r ω, X r ω, Y_future ω)) ⁻¹' ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))) := by
          rw [Measure.map_apply h_meas_future h_meas_rect]
      _ = μ {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j)} := by
          rw [h_pre_future]
      _ = μ {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)} :=
          h_cyl
      _ = μ ((fun ω => (Z_r ω, X r ω, Y_tail ω)) ⁻¹' ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))) := by
          rw [h_pre_tail]
      _ = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)) := by
          rw [Measure.map_apply h_meas_tail h_meas_rect]

  -- Apply π-λ theorem to extend from Rectangles to full σ-algebra
  -- Rectangles generate the product σ-algebra (from MeasureKernels.lean)
  have h_gen : (inferInstance : MeasurableSpace ((Fin r → α) × α × (Fin k → α)))
      = MeasurableSpace.generateFrom Rectangles := tripleRectangles_generate

  -- Define covering family (constant sequence of Set.univ)
  let Bseq : ℕ → Set ((Fin r → α) × α × (Fin k → α)) := fun _ => Set.univ

  have h1B : ⋃ n, Bseq n = Set.univ := by
    simp only [Bseq, Set.iUnion_const]

  have h2B : ∀ n, Bseq n ∈ Rectangles := by
    intro n
    refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
            Set.univ, MeasurableSet.univ,
            fun _ => Set.univ, fun _ => MeasurableSet.univ, ?_⟩
    ext ⟨z, y, c⟩
    simp only [Bseq, Set.mem_univ, Set.mem_prod, Set.mem_univ_pi]
    tauto

  have hμB : ∀ n, Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ (Bseq n) ≠ ⊤ := by
    intro n
    simp only [Bseq]
    exact measure_ne_top _ Set.univ

  -- Apply Measure.ext_of_generateFrom_of_iUnion
  exact Measure.ext_of_generateFrom_of_iUnion
    Rectangles Bseq h_gen h_pi h1B h2B hμB fun s hs => h_agree hs

/-! ### σ-Algebra Join Characterization -/

/-- Join with a finite future equals the comap of the paired map `(Z_r, θ_future^k)`. -/
lemma join_eq_comap_pair_finFuture
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r m k : ℕ) :
  firstRSigma X r ⊔ finFutureSigma X m k
    =
  MeasurableSpace.comap
    (fun ω => (fun i : Fin r => X i.1 ω,
               fun j : Fin k => X (m + 1 + j.1) ω))
    inferInstance := by
  classical
  -- Notation
  let f : Ω → (Fin r → α) := fun ω i => X i.1 ω
  let g : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.1) ω
  -- LHS is the join of comaps; RHS is comap of the product.
  have : firstRSigma X r = MeasurableSpace.comap f inferInstance := rfl
  have : finFutureSigma X m k = MeasurableSpace.comap g inferInstance := rfl
  -- `comap_prodMk` is exactly the identity we need.
  simpa [firstRSigma, finFutureSigma] using (MeasurableSpace.comap_prodMk f g).symm

end Exchangeability.DeFinetti.ViaMartingale
