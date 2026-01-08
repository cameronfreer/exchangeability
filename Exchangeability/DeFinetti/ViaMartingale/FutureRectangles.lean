/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations

/-!
# Future Rectangles and π-System Machinery

This file contains the π-λ theorem machinery for establishing measure equality
on future rectangles `B ×ˢ cylinder r C`.

## Main Results

* `contractable_dist_eq_on_first_r_tail` - Finite-dimensional cylinder equality
* `AgreeOnFutureRectangles` - Predicate for measures agreeing on future rectangles
* `measure_ext_of_future_rectangles` - π-λ extension theorem
* `contractable_dist_eq` - Full distributional equality from contractability

These are the key lemmas for the reverse martingale proof of de Finetti's theorem.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory

namespace Exchangeability.DeFinetti.ViaMartingale

open MartingaleHelpers

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Finite-Dimensional Cylinder Equality -/

/-- Finite-dimensional (cylinder) equality:
for any `r`, base set `B` and measurable sets on the first `r` tail coordinates,
the probabilities agree when comparing `(X m, θₘ X)` vs `(X k, θₘ X)`.

This is the exact finite-dimensional marginal needed for the martingale step. -/
lemma contractable_dist_eq_on_first_r_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m r : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
  classical
  let f : Fin r → ℕ := fun i => m + (i.1 + 1)
  have hf_mono : StrictMono f := by
    intro i j hij
    have hij' : i.1 < j.1 := (Fin.lt_iff_val_lt_val).1 hij
    have : i.1 + 1 < j.1 + 1 := Nat.succ_lt_succ hij'
    simp only [f]
    omega
  have hm_lt : ∀ i, m < f i := by
    intro i
    simp only [f]
    omega
  have hk_lt : ∀ i, k < f i := fun i => lt_of_le_of_lt hk (hm_lt i)
  let s₁ : Fin (r+1) → ℕ := Fin.cases m f
  let s₂ : Fin (r+1) → ℕ := Fin.cases k f
  have hs₁ : StrictMono s₁ := strictMono_fin_cases (n:=r) (f:=f) hf_mono hm_lt
  have hs₂ : StrictMono s₂ := strictMono_fin_cases (n:=r) (f:=f) hf_mono hk_lt
  have hmap_eq :
      Measure.map (fun ω i => X (s₁ i) ω) μ
        = Measure.map (fun ω i => X (s₂ i) ω) μ := by
    calc
      Measure.map (fun ω i => X (s₁ i) ω) μ
          = Measure.map (fun ω (i : Fin (r+1)) => X i.1 ω) μ := by
            simpa [s₁] using hX (r+1) s₁ hs₁
      _   = Measure.map (fun ω i => X (s₂ i) ω) μ := by
            simpa [s₂] using (hX (r+1) s₂ hs₂).symm
  let A : Set (Fin (r+1) → α) :=
    {v | v 0 ∈ B ∧ ∀ i : Fin r, v (Fin.succ i) ∈ C i}
  have hpre₁ :
      {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
        = (fun ω i => X (s₁ i) ω) ⁻¹' A := by
    ext ω; simp [A, s₁, f]
  have hpre₂ :
      {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
        = (fun ω i => X (s₂ i) ω) ⁻¹' A := by
    ext ω; simp [A, s₂, f]
  have hA : MeasurableSet A := by
    have h0 : Measurable (fun (v : Fin (r+1) → α) => v 0) := measurable_pi_apply 0
    have hS : ∀ i : Fin r, Measurable (fun (v : Fin (r+1) → α) => v (Fin.succ i)) :=
      fun i => measurable_pi_apply (Fin.succ i)
    have : A = (fun v => v 0) ⁻¹' B ∩ ⋂ i : Fin r, (fun v => v (Fin.succ i)) ⁻¹' C i := by
      ext v; simp [A, Set.mem_iInter]
    rw [this]
    exact (h0 hB).inter (MeasurableSet.iInter fun i => hS i (hC i))
  have hφ₁ : Measurable (fun ω i => X (s₁ i) ω) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact hX_meas m
    | succ j => simp only [s₁, f]; exact hX_meas (m + (j.1 + 1))
  have hφ₂ : Measurable (fun ω i => X (s₂ i) ω) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact hX_meas k
    | succ j => simp only [s₂, f]; exact hX_meas (m + (j.1 + 1))
  calc μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ ((fun ω i => X (s₁ i) ω) ⁻¹' A) := by rw [hpre₁]
    _ = (Measure.map (fun ω i => X (s₁ i) ω) μ) A := (Measure.map_apply hφ₁ hA).symm
    _ = (Measure.map (fun ω i => X (s₂ i) ω) μ) A := by rw [hmap_eq]
    _ = μ ((fun ω i => X (s₂ i) ω) ⁻¹' A) := Measure.map_apply hφ₂ hA
    _ = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by rw [← hpre₂]

/-! ## Rectangles using future tails and standard cylinders -/

section FutureRectangles

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Preimage calculation for rectangles with `(X k, θ_{m+1}X)` and a standard cylinder. -/
lemma preimage_rect_future
    (k m r : ℕ) (B : Set α) (C : Fin r → Set α) :
    let ψ := fun ω => (X k ω, shiftRV X (m + 1) ω)
    ψ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
      = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
  classical
  intro ψ
  ext ω; constructor <;> intro h
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      simpa only using (hC : (shiftRV X (m + 1) ω) ∈ cylinder (α:=α) r C) i
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      simpa only [ψ, shiftRV] using hC i

/-- **Finite-dimensional equality on future rectangles with standard cylinders.**
For `k ≤ m` and measurable `B`, the measures of
`B × cylinder r C` under the pushforwards by
`ω ↦ (X m ω, θ_{m+1}X(ω))` and `ω ↦ (X k ω, θ_{m+1}X(ω))` coincide. -/
lemma contractable_dist_eq_on_rectangles_future
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (r : ℕ) (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
        (B ×ˢ cylinder (α:=α) r C)
  =
    (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ)
        (B ×ˢ cylinder (α:=α) r C) := by
  classical
  set ψ₁ : Ω → α × (ℕ → α) := fun ω => (X m ω, shiftRV X (m + 1) ω)
  set ψ₂ : Ω → α × (ℕ → α) := fun ω => (X k ω, shiftRV X (m + 1) ω)
  have hrect : MeasurableSet (B ×ˢ cylinder (α:=α) r C) :=
    hB.prod (cylinder_measurable (α:=α) hC)
  have hpre₁ :
      ψ₁ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simp [ψ₁, preimage_rect_future (X:=X) m m r B C]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simp [ψ₂, preimage_rect_future (X:=X) k m r B C]
  have hfd :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      =
    μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    have := contractable_dist_eq_on_first_r_tail
        (μ:=μ) (X:=X) hX hX_meas k m r hk B hB C hC
    convert this using 2
  -- Show the sets are equal modulo arithmetic (m + 1 + i = m + (i + 1))
  have hset_eq (j : ℕ) : {ω | X j ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i}
                       = {ω | X j ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    simp only [Set.setOf_and]; congr 1; ext ω; simp only [Set.mem_setOf]
    exact forall_congr' fun i => by rw [show m + 1 + i.1 = m + (i.1 + 1) by omega]
  -- Apply Measure.map_apply with measurability of ψ₁ and ψ₂
  rw [Measure.map_apply ((hX_meas m).prodMk (measurable_shiftRV hX_meas)) hrect,
      Measure.map_apply ((hX_meas k).prodMk (measurable_shiftRV hX_meas)) hrect]
  rw [hpre₁, hpre₂, hset_eq m, hset_eq k]
  exact hfd

end FutureRectangles

/-- Two measures agree on all future rectangles (sets of form B ×ˢ cylinder r C). -/
def AgreeOnFutureRectangles (μ ν : Measure (α × (ℕ → α))) : Prop :=
  ∀ (r : ℕ) (B : Set α) (_hB : MeasurableSet B) (C : Fin r → Set α) (_hC : ∀ i, MeasurableSet (C i)),
    μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C)

lemma agree_on_future_rectangles_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m) :
    AgreeOnFutureRectangles
      (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
      (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ) := by
  intro r B hB C hC
  exact contractable_dist_eq_on_rectangles_future hX hX_meas k m hk r B hB C hC

/-! ## Measure extension from future rectangles -/

lemma measure_ext_of_future_rectangles
    {μ ν : Measure (α × (ℕ → α))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (r : ℕ) (B : Set α) (_hB : MeasurableSet B)
        (C : Fin r → Set α) (_hC : ∀ i, MeasurableSet (C i)),
        μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C)) :
    μ = ν := by
  classical
  -- π-system consisting of rectangles `B × cylinder r C`
  let S : Set (Set (α × (ℕ → α))) :=
    {s | ∃ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
          (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
          s = B ×ˢ cylinder (α:=α) r C}

  -- S is a π-system
  have h_pi : IsPiSystem S := by
    intro s₁ hs₁ s₂ hs₂ _
    obtain ⟨r₁, B₁, hB₁, C₁, hC₁, rfl⟩ := hs₁
    obtain ⟨r₂, B₂, hB₂, C₂, hC₂, rfl⟩ := hs₂
    let r := max r₁ r₂
    let C : Fin r → Set α := fun i =>
      if h1 : (i : ℕ) < r₁ then
        if h2 : (i : ℕ) < r₂ then C₁ ⟨i, h1⟩ ∩ C₂ ⟨i, h2⟩ else C₁ ⟨i, h1⟩
      else if h2 : (i : ℕ) < r₂ then C₂ ⟨i, h2⟩ else Set.univ
    have hC : ∀ i, MeasurableSet (C i) := by
      intro i
      classical
      by_cases h1 : (i : ℕ) < r₁
      · by_cases h2 : (i : ℕ) < r₂
        · have := (hC₁ ⟨i, h1⟩).inter (hC₂ ⟨i, h2⟩)
          simpa [C, h1, h2] using this
        · simpa [C, h1, h2] using hC₁ ⟨i, h1⟩
      · by_cases h2 : (i : ℕ) < r₂
        · simpa [C, h1, h2] using hC₂ ⟨i, h2⟩
        · simp [C, h1, h2]

    refine ⟨r, B₁ ∩ B₂, hB₁.inter hB₂, C, hC, ?_⟩
    ext ⟨a, f⟩; constructor
    · intro hmf
      rcases hmf with ⟨⟨hB₁', hC₁'⟩, ⟨hB₂', hC₂'⟩⟩
      refine ⟨⟨hB₁', hB₂'⟩, ?_⟩
      intro i
      classical
      by_cases h1 : (i : ℕ) < r₁
      · by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2]
          exact ⟨hC₁' ⟨i, h1⟩, hC₂' ⟨i, h2⟩⟩
        · simp [C, h1, h2]
          exact hC₁' ⟨i, h1⟩
      · by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2]
          exact hC₂' ⟨i, h2⟩
        · simp [C, h1, h2]
    · rintro ⟨⟨hB₁', hB₂'⟩, hC'⟩
      refine ⟨⟨hB₁', ?_⟩, ⟨hB₂', ?_⟩⟩
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_left r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h1 : (i : ℕ) < r₁ := i.2
        by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2] at this
          exact this.1
        · simpa [C, h1, h2] using this
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_right r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h2 : (i : ℕ) < r₂ := i.2
        by_cases h1 : (i : ℕ) < r₁
        · simp [C, h1, h2] at this
          exact this.2
        · simpa [C, h1, h2] using this

  -- Show that S generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace (α × (ℕ → α)))
      = MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · -- (⊆) Product σ-algebra ≤ generateFrom S
      have h_fst : ∀ A : Set α, MeasurableSet A →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.fst ⁻¹' A) := by
        intro A hA
        have : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set (ℕ → α)) := by
          ext ⟨a, f⟩; simp
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨0, A, hA, (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
        ext ⟨a, f⟩
        simp only [Set.mem_prod, Set.mem_univ, and_true]
        show a ∈ A ↔ a ∈ A ∧ f ∈ MartingaleHelpers.cylinder 0 (fun _ => Set.univ)
        rw [MartingaleHelpers.cylinder]
        simp

      have h_snd : ∀ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.snd ⁻¹' MartingaleHelpers.cylinder r C) := by
        intro r C hC
        have : (Prod.snd : α × (ℕ → α) → ℕ → α) ⁻¹' MartingaleHelpers.cylinder r C
            = Set.univ ×ˢ MartingaleHelpers.cylinder r C := by
          ext ⟨a, f⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
        rw [this]
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨r, Set.univ, MeasurableSet.univ, C, hC, rfl⟩

      have h_fst_comap : MeasurableSpace.comap (Prod.fst : α × (ℕ → α) → α) inferInstance
          ≤ MeasurableSpace.generateFrom S := by
        intro s hs
        obtain ⟨A, hA, rfl⟩ := hs
        exact h_fst A hA

      have h_snd_comap : MeasurableSpace.comap (Prod.snd : α × (ℕ → α) → ℕ → α) inferInstance
          ≤ MeasurableSpace.generateFrom S := by
        rw [← measurable_iff_comap_le]
        let T : Set (Set (ℕ → α)) := {s | ∃ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) ∧ s = cylinder r C}

        have hT_gen : (inferInstance : MeasurableSpace (ℕ → α)) = MeasurableSpace.generateFrom T := by
          apply le_antisymm
          · have h_coord_meas : ∀ (i : ℕ) (A : Set α), MeasurableSet A →
                MeasurableSet[MeasurableSpace.generateFrom T] ((fun f : ℕ → α => f i) ⁻¹' A) := by
              intro i A hA
              let r := i + 1
              let C : Fin r → Set α := fun j => if j.val = i then A else Set.univ
              have hC_meas : ∀ j, MeasurableSet (C j) := by
                intro j
                simp only [C]
                split_ifs
                · exact hA
                · exact MeasurableSet.univ
              have h_eq : ((fun f : ℕ → α => f i) ⁻¹' A) = MartingaleHelpers.cylinder r C := by
                ext f
                simp only [C, r, Set.mem_preimage, MartingaleHelpers.cylinder]
                constructor
                · intro hf j
                  by_cases h : j.val = i
                  · simp [h]; exact hf
                  · simp [h]
                · intro hf
                  simpa using hf ⟨i, Nat.lt_succ_self i⟩
              rw [h_eq]
              apply MeasurableSpace.measurableSet_generateFrom
              exact ⟨r, C, hC_meas, rfl⟩
            rw [MeasurableSpace.pi_eq_generateFrom_projections]
            apply MeasurableSpace.generateFrom_le
            intro s hs
            obtain ⟨i, A, hA, rfl⟩ := hs
            exact h_coord_meas i A hA
          · apply MeasurableSpace.generateFrom_le
            intro s
            rintro ⟨n, coords, coords_meas, rfl⟩
            exact cylinder_measurable coords_meas

        have : @Measurable (α × (ℕ → α)) (ℕ → α)
            (MeasurableSpace.generateFrom S) (MeasurableSpace.generateFrom T) Prod.snd := by
          apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom S) _ _
          intro s hs
          obtain ⟨r, C, hC, rfl⟩ := hs
          exact h_snd r C hC
        rw [← hT_gen] at this
        exact this

      calc (inferInstance : MeasurableSpace (α × (ℕ → α)))
          = MeasurableSpace.comap Prod.fst inferInstance
            ⊔ MeasurableSpace.comap Prod.snd inferInstance := by
              rfl
        _ ≤ MeasurableSpace.generateFrom S :=
              sup_le h_fst_comap h_snd_comap
    · apply MeasurableSpace.generateFrom_le
      intro t ht
      obtain ⟨r, B, hB, C, hC, rfl⟩ := ht
      exact hB.prod (cylinder_measurable hC)

  have h_agree : ∀ s ∈ S, μ s = ν s := by
    intro s hs
    rcases hs with ⟨r, B, hB, C, hC, rfl⟩
    exact h r B hB C hC

  let Bseq : ℕ → Set (α × (ℕ → α)) := fun _ => Set.univ
  have h1B : ⋃ n, Bseq n = Set.univ := by
    simp only [Bseq, Set.iUnion_const]
  have h2B : ∀ n, Bseq n ∈ S := by
    intro n
    refine ⟨0, Set.univ, MeasurableSet.univ,
      (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
    ext ⟨a, f⟩
    simp only [Bseq, Set.mem_prod, Set.mem_univ, true_and, MartingaleHelpers.cylinder]
    simp
  have hμB : ∀ n, μ (Bseq n) ≠ ⊤ := by
    intro n
    simp only [Bseq]
    exact measure_ne_top μ Set.univ

  exact Measure.ext_of_generateFrom_of_iUnion
    S Bseq h_gen h_pi h1B h2B hμB h_agree

/-- Helper lemma: contractability gives the key distributional equality.

If `X` is contractable, then for any `k ≤ m`:
```
(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)
```
where `θ_{m+1} X` drops the first coordinate and keeps the *future* tail
`ω ↦ (n ↦ X(m + 1 + n) ω)`. -/
lemma contractable_dist_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m) :
    Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ
      = Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ := by
  apply measure_ext_of_future_rectangles
  intro r B hB C hC
  exact contractable_dist_eq_on_rectangles_future hX hX_meas k m hk r B hB C hC

/-- Measures that agree on all future rectangles are equal. -/
lemma AgreeOnFutureRectangles_to_measure_eq
    {μ ν : Measure (α × (ℕ → α))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : AgreeOnFutureRectangles μ ν) : μ = ν :=
  measure_ext_of_future_rectangles h

end Exchangeability.DeFinetti.ViaMartingale
