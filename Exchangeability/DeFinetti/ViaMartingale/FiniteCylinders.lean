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
      ext f
      simp only [S, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf]
      tauto

    rw [h_decomp]
    apply MeasurableSet.inter
    · apply MeasurableSet.inter
      · apply MeasurableSet.iInter
        intro i
        exact measurable_pi_apply (Fin.mk i.val (by omega)) (hA i)
      · exact measurable_pi_apply (Fin.mk r (by omega)) hB
    · apply MeasurableSet.iInter
      intro j
      exact measurable_pi_apply (Fin.mk (r + 1 + j.val) (by omega)) (hC j)

  -- Prove the functions are measurable
  have h_meas_idx : Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) := by
    fun_prop (disch := measurability)
  have h_meas_std : Measurable (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) := by
    fun_prop (disch := measurability)

  calc μ ((fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) ⁻¹' S)
      = Measure.map (fun ω i => X (idx i) ω) μ S := by
        rw [Measure.map_apply h_meas_idx hS_meas]
    _ = Measure.map (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) μ S := by
        rw [contract]
    _ = μ ((fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) ⁻¹' S) := by
        rw [Measure.map_apply h_meas_std hS_meas]

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
  -- Define cylinder rectangles generating the product σ-algebra.
  let Rectangles :
      Set (Set ((Fin r → α) × α × (Fin k → α))) :=
    {S | ∃ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
          (B : Set α) (hB : MeasurableSet B)
          (C : Fin k → Set α) (hC : ∀ j, MeasurableSet (C j)),
        S = (Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)}

  -- Rectangles form a π-system.
  have h_pi : IsPiSystem Rectangles := by
    intro S₁ hS₁ S₂ hS₂ h_ne
    rcases hS₁ with ⟨A₁, hA₁, B₁, hB₁, C₁, hC₁, rfl⟩
    rcases hS₂ with ⟨A₂, hA₂, B₂, hB₂, C₂, hC₂, rfl⟩
    refine ⟨fun i => A₁ i ∩ A₂ i, ?_, B₁ ∩ B₂, hB₁.inter hB₂,
            fun j => C₁ j ∩ C₂ j, ?_, ?_⟩
    · intro i; exact (hA₁ i).inter (hA₂ i)
    · intro j; exact (hC₁ j).inter (hC₂ j)
    · ext ⟨z, y, c⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ_pi]
      constructor
      · intro ⟨⟨hz1, hy1, hc1⟩, hz2, hy2, hc2⟩
        exact ⟨fun i => ⟨hz1 i, hz2 i⟩, ⟨hy1, hy2⟩, fun j => ⟨hc1 j, hc2 j⟩⟩
      · intro ⟨hz, hy, hc⟩
        exact ⟨⟨fun i => (hz i).1, hy.1, fun j => (hc j).1⟩, fun i => (hz i).2, hy.2, fun j => (hc j).2⟩

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
  -- Show that Rectangles generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace ((Fin r → α) × α × (Fin k → α)))
      = MeasurableSpace.generateFrom Rectangles := by
    -- Two-sided inclusion
    apply le_antisymm
    · -- (⊆) Product σ-algebra ≤ generateFrom Rectangles
      -- The product σ-algebra on (Fin r → α) × α × (Fin k → α) is generated by the three projections.
      -- We show each projection is measurable w.r.t. generateFrom Rectangles.

      -- First projection: (Fin r → α)
      have h_fst : ∀ (A : Fin r → Set α), (∀ i, MeasurableSet (A i)) →
          MeasurableSet[MeasurableSpace.generateFrom Rectangles]
            (Prod.fst ⁻¹' (Set.univ.pi A)) := by
        intro A hA
        -- Prod.fst ⁻¹' (pi A) = (pi A) × univ × univ
        have : (Prod.fst : (Fin r → α) × α × (Fin k → α) → (Fin r → α)) ⁻¹' (Set.univ.pi A) =
            (Set.univ.pi A) ×ˢ (Set.univ : Set α) ×ˢ (Set.univ.pi (fun (_ : Fin k) => Set.univ)) := by
          ext ⟨z, y, c⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi, Set.mem_univ, true_and]
          tauto
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨A, hA, Set.univ, MeasurableSet.univ,
                fun _ => Set.univ, fun _ => MeasurableSet.univ, rfl⟩

      -- Second projection (middle component): α
      have h_fst_snd : ∀ (B : Set α), MeasurableSet B →
          MeasurableSet[MeasurableSpace.generateFrom Rectangles]
            ((Prod.fst ∘ Prod.snd) ⁻¹' B) := by
        intro B hB
        -- (Prod.fst ∘ Prod.snd) ⁻¹' B = univ × B × univ
        have : (Prod.fst ∘ Prod.snd : (Fin r → α) × α × (Fin k → α) → α) ⁻¹' B =
            (Set.univ.pi (fun (_ : Fin r) => Set.univ)) ×ˢ B ×ˢ
            (Set.univ.pi (fun (_ : Fin k) => Set.univ)) := by
          ext ⟨z, y, c⟩
          simp only [Set.mem_preimage, Function.comp_apply, Set.mem_prod,
                     Set.mem_univ_pi, Set.mem_univ]
          tauto
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
                B, hB, fun _ => Set.univ, fun _ => MeasurableSet.univ, rfl⟩

      -- Third projection: (Fin k → α)
      have h_snd_snd : ∀ (C : Fin k → Set α), (∀ j, MeasurableSet (C j)) →
          MeasurableSet[MeasurableSpace.generateFrom Rectangles]
            ((Prod.snd ∘ Prod.snd) ⁻¹' (Set.univ.pi C)) := by
        intro C hC
        -- (Prod.snd ∘ Prod.snd) ⁻¹' (pi C) = univ × univ × (pi C)
        have : (Prod.snd ∘ Prod.snd : (Fin r → α) × α × (Fin k → α) → Fin k → α) ⁻¹'
            (Set.univ.pi C) =
            (Set.univ.pi (fun (_ : Fin r) => Set.univ)) ×ˢ Set.univ ×ˢ (Set.univ.pi C) := by
          ext ⟨z, y, c⟩
          simp only [Set.mem_preimage, Function.comp_apply, Set.mem_prod,
                     Set.mem_univ_pi, Set.mem_univ]
          tauto
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ,
                Set.univ, MeasurableSet.univ, C, hC, rfl⟩

      -- Now show that the comap of each projection is ≤ generateFrom Rectangles
      -- For the first projection (Pi space)
      have h_fst_comap : MeasurableSpace.comap Prod.fst inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        rw [← measurable_iff_comap_le]
        -- Show Prod.fst is measurable w.r.t. generateFrom Rectangles
        -- The Pi σ-algebra on (Fin r → α) is generated by coordinate projections
        rw [MeasurableSpace.pi_eq_generateFrom_projections (ι := Fin r) (α := fun _ => α)]
        apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom Rectangles) _ _
        intro s hs
        -- s is a coordinate preimage: ∃ i A, MeasurableSet A ∧ eval i ⁻¹' A = s
        obtain ⟨i, A, hA, rfl⟩ := hs
        -- Show Prod.fst ⁻¹' (eval i ⁻¹' A) is in generateFrom Rectangles
        -- eval i ⁻¹' A = pi (fun j => if j = i then A else univ)
        let C : Fin r → Set α := fun j => if j = i then A else Set.univ
        have hC : ∀ j, MeasurableSet (C j) := by
          intro j; simp only [C]; split_ifs; exact hA; exact MeasurableSet.univ
        have : (fun f : Fin r → α => f i) ⁻¹' A = Set.univ.pi C := by
          ext f; simp only [C, Set.mem_preimage, Set.mem_univ_pi]
          constructor
          · intro hf j
            by_cases h : j = i
            · simp [h]; exact hf
            · simp [h]
          · intro hf; simpa using hf i
        rw [this]
        exact h_fst C hC

      -- For the second projection (middle component)
      have h_fst_snd_comap : MeasurableSpace.comap (Prod.fst ∘ Prod.snd) inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        intro s hs
        obtain ⟨B, hB, rfl⟩ := hs
        exact h_fst_snd B hB

      -- For the third projection (Pi space)
      have h_snd_snd_comap : MeasurableSpace.comap (Prod.snd ∘ Prod.snd) inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        rw [← measurable_iff_comap_le]
        rw [MeasurableSpace.pi_eq_generateFrom_projections (ι := Fin k) (α := fun _ => α)]
        apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom Rectangles) _ _
        intro s hs
        obtain ⟨j, C, hC, rfl⟩ := hs
        let D : Fin k → Set α := fun i => if i = j then C else Set.univ
        have hD : ∀ i, MeasurableSet (D i) := by
          intro i; simp only [D]; split_ifs; exact hC; exact MeasurableSet.univ
        have : (fun f : Fin k → α => f j) ⁻¹' C = Set.univ.pi D := by
          ext f; simp only [D, Set.mem_preimage, Set.mem_univ_pi]
          constructor
          · intro hf i
            by_cases h : i = j
            · simp [h]; exact hf
            · simp [h]
          · intro hf; simpa using hf j
        rw [this]
        exact h_snd_snd D hD

      -- Use measurability of the three projections to show all sets are in generateFrom Rectangles
      -- For A × B × C = A × (B × C), the product σ-algebra is generated by both projections
      have : (inferInstance : MeasurableSpace ((Fin r → α) × α × (Fin k → α))) =
          MeasurableSpace.comap Prod.fst inferInstance ⊔
          MeasurableSpace.comap Prod.snd inferInstance := rfl
      rw [this]
      -- Now Prod.snd gives us B × C, which is also a product
      have h_snd_le : MeasurableSpace.comap (Prod.snd : (Fin r → α) × α × (Fin k → α) → α × (Fin k → α)) inferInstance
          ≤ MeasurableSpace.generateFrom Rectangles := by
        -- Prod.snd σ-algebra is generated by Prod.fst and Prod.snd on the second component
        calc MeasurableSpace.comap (Prod.snd : (Fin r → α) × α × (Fin k → α) → α × (Fin k → α)) inferInstance
            = MeasurableSpace.comap Prod.snd
                (MeasurableSpace.comap Prod.fst inferInstance ⊔
                 MeasurableSpace.comap Prod.snd inferInstance) := by rfl
          _ = MeasurableSpace.comap Prod.snd (MeasurableSpace.comap Prod.fst inferInstance)
              ⊔ MeasurableSpace.comap Prod.snd (MeasurableSpace.comap Prod.snd inferInstance) := by
                rw [MeasurableSpace.comap_sup]
          _ = MeasurableSpace.comap (Prod.fst ∘ Prod.snd) inferInstance
              ⊔ MeasurableSpace.comap (Prod.snd ∘ Prod.snd) inferInstance := by
                rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
          _ ≤ MeasurableSpace.generateFrom Rectangles :=
                sup_le h_fst_snd_comap h_snd_snd_comap
      exact sup_le h_fst_comap h_snd_le

    · -- (⊇) generateFrom Rectangles ≤ Product σ-algebra
      -- Every rectangle is measurable in the product σ-algebra
      apply MeasurableSpace.generateFrom_le
      intro t ht
      obtain ⟨A, hA, B, hB, C, hC, rfl⟩ := ht
      -- (pi A) × B × (pi C) is measurable as a product of measurable sets
      exact (MeasurableSet.univ_pi hA).prod (hB.prod (MeasurableSet.univ_pi hC))

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

  -- Convert h_agree to explicit form for Measure.ext_of_generateFrom_of_iUnion
  have h_agree_explicit : ∀ s ∈ Rectangles,
      Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ s
        = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ s := by
    intro s hs
    exact h_agree hs

  -- Apply Measure.ext_of_generateFrom_of_iUnion
  exact Measure.ext_of_generateFrom_of_iUnion
    Rectangles Bseq h_gen h_pi h1B h2B hμB h_agree_explicit

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
