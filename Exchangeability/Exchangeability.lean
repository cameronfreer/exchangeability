/-- Exchangeability for infinite sequences.

This file reuses the basic definitions from `Exchangeability/Contractability.lean`
and focuses on the Kolmogorov-style equivalence between exchangeability and full
exchangeability.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Exchangeability.Contractability

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Auxiliary lemma: probability measures on path space are determined by their
finite-dimensional marginals. -/
lemma measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ (n : ℕ) (S : Set (Fin n → α)) (hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ S =
          Measure.map (fun f : ℕ → α => fun i : Fin n => f i) ν S) :
    μ = ν := by
  classical
  refine Measure.ext_of_generate_finite (measurableCylinders fun _ : ℕ => α)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro T hT
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hT
    let bound : ℕ := I.sup id
    let m : ℕ := bound + 1
    have hlt_of_mem : ∀ {i : ℕ}, i ∈ I → i < m := by
      intro i hi
      have : i ≤ bound := Finset.le_sup hi
      exact Nat.lt_of_le_of_lt this (Nat.lt_succ_self _)
    let emb : I → Fin m := fun i => ⟨i.1, hlt_of_mem i.2⟩
    let restrictToI : (Fin m → α) → (∀ i : I, α) := fun g i => g (emb i)
    have h_restrict_meas : Measurable restrictToI :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (emb i))
    let S' : Set (Fin m → α) := restrictToI ⁻¹' S
    have hS' : MeasurableSet S' := hS.preimage h_restrict_meas
    have hcyl : cylinder I S
        = (fun f : ℕ → α => fun i : Fin m => f i) ⁻¹' S' := by
      ext f; constructor
      · intro hf
        have : I.restrict f ∈ S := by simpa [cylinder] using hf
        have hrestrict : restrictToI (fun i : Fin m => f i) = I.restrict f := by
          ext i; simp [restrictToI, emb]
        simpa [S', hrestrict]
      · intro hf
        have hrestrict : restrictToI (fun i : Fin m => f i) = I.restrict f := by
          ext i; simp [restrictToI, emb]
        have : restrictToI (fun i : Fin m => f i) ∈ S := by
          simpa [S', hrestrict] using hf
        simpa [cylinder] using this
    have hproj : Measurable fun f : ℕ → α => fun i : Fin m => f i :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply i)
    have h_evalμ : μ (cylinder I S)
        = Measure.map (fun f : ℕ → α => fun i : Fin m => f i) μ S' := by
      simpa [hcyl, S', Measure.map_apply hproj hS']
    have h_evalν : ν (cylinder I S)
        = Measure.map (fun f : ℕ → α => fun i : Fin m => f i) ν S' := by
      simpa [hcyl, S', Measure.map_apply hproj hS']
    have h_eq := h m S' hS'
    simpa [h_evalμ, h_evalν]
  ·
    have hμ : μ Set.univ = 1 := IsProbabilityMeasure.measure_univ (μ:=μ)
    have hν : ν Set.univ = 1 := IsProbabilityMeasure.measure_univ (μ:=ν)
    simpa [hμ, hν]

/-- Exchangeability implies full exchangeability (Kolmogorov extension theorem).

For an exchangeable family `X`, the finite-dimensional distributions satisfy the
consistency conditions required by Kolmogorov's extension theorem. This allows us
to construct a unique probability measure on the infinite product space such that
the process is fully exchangeable.

**Proof strategy**: Use mathlib's Ionescu-Tulcea theorem (`ProbabilityTheory.Kernel.traj`),
which constructs infinite products of probability kernels. For the constant kernel
case (which suffices here), the finite-dimensional distributions of an exchangeable
process satisfy the required consistency conditions, and the Ionescu-Tulcea
construction yields a unique measure on the infinite product that is invariant
under all permutations.
-/
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsProbabilityMeasure μ] (hX_meas : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ FullyExchangeable μ X := by
  constructor
  · intro hexch π
    -- Strategy: Use uniqueness from Ionescu-Tulcea/Kolmogorov extension

    -- Step 1: Define the pushforward measures for X and X ∘ π
    let μ_X := Measure.map (fun ω => fun n : ℕ => X n ω) μ
    let μ_Xπ := Measure.map (fun ω => fun n : ℕ => X (π n) ω) μ

    -- Step 2: Both are probability measures on ℕ → α
    -- These instances are needed for the finite measure uniqueness arguments in h_unique.
    have hμ_X : IsProbabilityMeasure μ_X := by
      -- Pushforward of probability measure is probability measure
      constructor
      show μ_X Set.univ = 1
      simp only [μ_X, Measure.map_apply (measurable_pi_lambda _ (fun i => hX_meas i)) MeasurableSet.univ]
      simp
    have hμ_Xπ : IsProbabilityMeasure μ_Xπ := by
      -- Pushforward of probability measure is probability measure
      constructor
      show μ_Xπ Set.univ = 1
      simp only [μ_Xπ, Measure.map_apply (measurable_pi_lambda _ (fun i => hX_meas (π i))) MeasurableSet.univ]
      simp

    -- Step 3: Show finite-dimensional marginals agree
    have h_marginals : ∀ (n : ℕ) (S : Set (Fin n → α)) (hS : MeasurableSet S),
        μ_X.map (fun f : ℕ → α => fun i : Fin n => f i) S =
        μ_Xπ.map (fun f : ℕ → α => fun i : Fin n => f i) S := by
      intro n S hS
      classical
      -- Finite set of indices appearing in the first `n` coordinates of `π`.
      let indices : Finset ℕ := (Finset.range n).image fun i => π i
      -- Upper bound for these indices.
      let bound : ℕ := indices.sup id
      -- Work inside a finite initial segment large enough to contain the indices.
      let m : ℕ := max n (bound + 1)
      have hnm : n ≤ m := le_max_left _ _
      have hbound_le : ∀ {x : ℕ}, x ∈ indices → x ≤ bound := fun hx =>
        Finset.le_sup hx
      have hπ_le_bound : ∀ i : Fin n, π i.val ≤ bound := by
        intro i
        exact hbound_le (by
          refine Finset.mem_image.mpr ?_
          refine ⟨i.val, ?_, ?_⟩
          · exact Finset.mem_range.mpr i.is_lt
          · simp)
      have hπ_lt : ∀ i : Fin n, π i.val < m := by
        intro i
        have hlt : π i.val < bound + 1 := lt_of_le_of_lt (hπ_le_bound i) (lt_add_one _)
        exact lt_of_lt_of_le hlt (le_max_right _ _)
      have hπ_mem : ∀ i : Fin n, π i.val ∈ indices := by
        intro i
        refine Finset.mem_image.mpr ?_
        refine ⟨i.val, ?_, ?_⟩
        · exact Finset.mem_range.mpr i.is_lt
        · simp
      have h_symm_lt : ∀ {x : ℕ}, x ∈ indices → π.symm x < n := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hk_lt : k < n := Finset.mem_range.mp hk
        simpa using hk_lt
      -- Inclusion of `Fin n` into `Fin m`.
      let ι : Fin n → Fin m := Fin.castLEEmb hnm
      -- Subsets corresponding to the first `n` coordinates and their images under `π`.
      let p : Fin m → Prop := fun x => x.val < n
      let q : Fin m → Prop := fun x => x.val ∈ indices
      have hnm' : n ≤ m := hnm
      have hlt_of_lt : ∀ {i : ℕ}, i < n → i < m := fun hi => lt_of_lt_of_le hi hnm'
      -- Equivalence between the two subtypes, sending `i` to `π i`.
      let e : {x : Fin m // p x} ≃ {x : Fin m // q x} :=
        { toFun :=
            fun x =>
              let i : Fin n := ⟨x.1.val, x.2⟩
              ⟨⟨π i.val, hπ_lt i⟩, hπ_mem i⟩
          , invFun :=
            fun y =>
              let i := π.symm y.1.val
              have hi_lt : i < n := h_symm_lt y.2
              ⟨⟨i, hlt_of_lt hi_lt⟩, hi_lt⟩
          , left_inv := by
              rintro ⟨x, hx⟩
              ext
              -- Reduce to the underlying natural numbers.
              dsimp [p] at hx
              simp [ι, e, hx, hlt_of_lt, Fin.castLEEmb, Function.comp, hπ_lt]
            , right_inv := by
              rintro ⟨y, hy⟩
              ext
              have hy' : π.symm y.val < n := h_symm_lt hy
              simp [q, e, hy, hy', hlt_of_lt, hπ_lt, Fin.castLEEmb] }
      -- Extend this equivalence to a permutation of `Fin m`.
      let σ : Equiv.Perm (Fin m) := Equiv.extendSubtype e
      have hσ_apply : ∀ i : Fin n, σ (ι i) = ⟨π i.val, hπ_lt i⟩ := by
        intro i
        have hi : p (ι i) := by
          dsimp [p, ι, Fin.castLEEmb]
          simpa using i.is_lt
        have hi' : (ι i).val = i.val := by
          dsimp [ι, Fin.castLEEmb]
          rfl
        have := Equiv.extendSubtype_apply_of_mem (e:=e) (x:=ι i) hi
        -- Evaluate `e` on the corresponding subtype element.
        simp [e, ι, hi, hi', hπ_lt, hπ_mem, Fin.castLEEmb] at this
        exact this
      -- Define the maps on path space before and after applying `σ`.
      let f : Ω → (Fin m → α) := fun ω j => X j.val ω
      let g : Ω → (Fin m → α) := fun ω j => X (σ j).val ω
      have hf : Measurable f :=
        measurable_pi_lambda _ (fun j => hX_meas j.val)
      have hg : Measurable g :=
        measurable_pi_lambda _ (fun j => hX_meas (σ j).val)
      -- Restrict functions on `Fin m` to the first `n` coordinates.
      let restrict : (Fin m → α) → (Fin n → α) := fun h i => h (ι i)
      have hrestrict : Measurable restrict :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply (ι i))
      -- Exchangeability on `Fin m` with permutation `σ`.
      have h_exchange := hexch m σ
      -- Push this equality forward along `restrict`.
      have h_push := congrArg (fun ν => Measure.map restrict ν) h_exchange
      have h_map_g : Measure.map restrict (Measure.map g μ)
            = Measure.map (restrict ∘ g) μ := by
        simpa [Function.comp] using
          (Measure.map_map (μ:=μ) (f:=g) (g:=restrict) (hg:=hrestrict) (hf:=hg))
      have h_map_f : Measure.map restrict (Measure.map f μ)
            = Measure.map (restrict ∘ f) μ := by
        simpa [Function.comp] using
          (Measure.map_map (μ:=μ) (f:=f) (g:=restrict) (hg:=hrestrict) (hf:=hf))
      have h_paths : Measure.map (restrict ∘ g) μ = Measure.map (restrict ∘ f) μ := by
        simpa [h_map_g, h_map_f] using h_push
      -- Evaluate both sides explicitly.
      have h_comp_g : restrict ∘ g = fun ω => fun i : Fin n => X (π i.val) ω := by
        funext ω i
        dsimp [restrict, g, Function.comp]
        have := hσ_apply i
        simpa [ι, Fin.castLEEmb] using congrArg (fun (t : Fin m) => X t.val ω) this
      have h_comp_f : restrict ∘ f = fun ω => fun i : Fin n => X i.val ω := by
        funext ω i
        dsimp [restrict, f, Function.comp, ι, Fin.castLEEmb]
      -- Conclude the equality of the finite-dimensional marginals.
      have := congrArg (fun ν => ν S) (by simpa [h_comp_g, h_comp_f] using h_paths)
      simpa using this

    -- Step 4: Kolmogorov uniqueness via π-λ theorem
    have h_unique : μ_X = μ_Xπ :=
      measure_eq_of_fin_marginals_eq (μ:=μ_X) (ν:=μ_Xπ) (h:=h_marginals)

    -- Step 5: Conclude equal laws
    calc
      Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ
          = μ_Xπ := rfl
      _ = μ_X := h_unique.symm
      _ = Measure.map (fun ω => fun i : ℕ => X i ω) μ := rfl
  · intro hfull
    exact FullyExchangeable.exchangeable hX_meas hfull

end Exchangeability
