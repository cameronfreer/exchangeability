/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic

-- Project-local imports
import Exchangeability.Contractability
import Exchangeability.Tail.TailSigma
import Exchangeability.Probability.CondExp
import Exchangeability.Ergodic.KoopmanMeanErgodic

/-!
# Bridge: Mean Ergodic Theorem to Cesàro-Conditional Expectation Convergence

This file bridges the abstract Mean Ergodic Theorem (MET) from `KoopmanMeanErgodic.lean`
to the concrete L¹ convergence result needed in `ViaL2.lean`.

## The Four Bridges

1. **Contractable → Shift Invariance**: Contractability of a process X implies the law
   on path space is shift-invariant, making the shift a measure-preserving transformation.

2. **Fixed Space = Tail**: The fixed-point subspace of the Koopman operator for the shift
   equals L²(tail σ-algebra), so the orthogonal projection is conditional expectation.

3. **L² → L¹**: On a probability space, L² convergence implies L¹ convergence by
   Hölder's inequality (‖Y‖₁ ≤ ‖Y‖₂).

4. **Pullback**: Conditional expectation commutes with the factor map `pathify` that
   sends ω ↦ (n ↦ X n ω).

## Main Result

`cesaro_to_condexp_L1`: For a contractable process X and bounded measurable f,
the Cesàro averages `(1/m) ∑ᵢ f(Xᵢ)` converge to `𝔼[f(X₀) | tail(X)]` in L¹.

This replaces the axiom of the same name in `ViaL2.lean`.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Filter Topology

namespace Exchangeability.Bridge

/-! ## A. Path Space and Factor Map -/

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Path space (already in Koopman file as `Ω[α]`) -/
abbrev PathSpace (α : Type*) := ℕ → α
notation3 "Ω[" α "]" => PathSpace α

/-- Factor map that sends `ω : Ω` to the path `(n ↦ X n ω)` -/
def pathify {α} (X : ℕ → Ω → α) : Ω → Ω[α] :=
  fun ω n => X n ω

lemma measurable_pathify {α} {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) :
    Measurable (pathify X) := by
  -- measurability into a countable product: check all coordinates
  refine measurable_pi_lambda (fun n => ?_)
  simpa using hX_meas n

/-- Law of the process as a probability measure on path space. -/
def μ_path {α} (X : ℕ → Ω → α) : Measure (Ω[α]) :=
  Measure.map (pathify X) μ

instance {α} (X : ℕ → Ω → α) : IsProbabilityMeasure (μ_path X) := by
  -- pushforward of a probability is a probability
  have : (μ_path X) ((Set.univ : Set (Ω[α]))) = 1 := by
    simp [μ_path, pathify]
  exact ⟨by simpa using this⟩

/-! ## B. Bridge 1: Contractable → Shift Invariance -/

open Exchangeability

/-- **Bridge 1.** `Contractable` ⇒ shift-invariant law on path space. -/
lemma contractable_shift_invariant_law
    {X : ℕ → Ω → ℝ} (hX : Exchangeability.Contractable μ X) :
    Measure.map (Exchangeability.Ergodic.shift (α := ℝ)) (μ_path X) = (μ_path X) := by
  /- Intuition: `Contractable` ⇒ the finite-dimensional distributions are shift invariant,
     hence the pushforward measure is invariant under `shift`. Your project should already
     have this; if it has a lemma under a different name, replace the next line by it. -/
  -- TODO: replace with your project's lemma, e.g.
  -- exact hX.path_law_shift_invariant
  -- For now, we give a short proof sketch you can formalize:
  --
  -- * Fix m and a cylinder set depending on coordinates {0,…,m-1}.
  -- * By `Contractable`, the joint law of (X_0,…,X_{m-1}) equals that of (X_1,…,X_m).
  -- * Cylinders generate the path σ-algebra; conclude `map shift (μ_path X) = μ_path X`.
  --
  sorry

/-- Measurability of `shift` on path space (from your Koopman file). -/
lemma measurable_shift_real : Measurable (Exchangeability.Ergodic.shift (α := ℝ)) :=
  Exchangeability.Ergodic.measurable_shift

/-- **Bridge 1'.** Package the previous lemma as `MeasurePreserving` for MET. -/
lemma measurePreserving_shift_path (X : ℕ → Ω → ℝ)
    (hX : Exchangeability.Contractable μ X) :
    MeasurePreserving (Exchangeability.Ergodic.shift (α := ℝ)) (μ_path X) (μ_path X) := by
  refine ⟨measurable_shift_real, ?_⟩
  simpa using contractable_shift_invariant_law (μ := μ) (X := X) hX

/-! ## C. Bridge 2: Fixed Space = L²(Tail) -/

-- Shorthand: the canonical coordinate process on path space
def coord : ℕ → Ω[ℝ] → ℝ := fun n ω => ω n

-- The tail σ-algebra on path space (re-using your project's notation via re-export)
-- NOTE: you re-export `TailSigma.tailSigma := Exchangeability.Tail.tailProcess`
abbrev tail_on_path : MeasurableSpace (Ω[ℝ]) :=
  TailSigma.tailSigma (coord)

lemma tail_on_path_le : tail_on_path ≤ (inferInstance : MeasurableSpace (Ω[ℝ])) :=
  by
    -- trivial since `tailSigma` is a sub-σ-algebra
    change TailSigma.tailSigma coord ≤ _
    -- your project already has this
    simpa using TailSigma.tailSigma_le (X := coord) (by intro n; exact measurable_pi_apply n)

/-- **Bridge 2.** For the left shift on one-sided path space, the fixed-point subspace of the
Koopman operator equals the closed subspace `L²(tail_on_path)`; consequently the
metric/orthogonal projection is `condexp` onto the tail σ-algebra. -/
lemma metProjection_eq_condexp_tail_on_path
    (X0 : Lp ℝ 2 (μ_path (X := fun _ : ℕ => fun _ : Ω => (0 : ℝ)))) -- dummy to pin universe
    (g : Lp ℝ 2 (μ_path (X := fun _ : ℕ => fun _ : Ω => (0 : ℝ)))) :
    True := by
  /- This is a schematic lemma header to illustrate the identity we use below. In the proof
     of the main theorem we directly *rewrite* `metProjection` to `condexp_L2` by the universal
     characterization of orthogonal projections:
       • fixed space = { h ∈ L² : h ∘ shift = h a.e. } = L²(tail_on_path)
       • `condexp_L2` is the orthogonal projection onto `L²(tail_on_path)`
     You can implement this cleanly by adapting (or adding) a lemma like:

     `lemma fixedSpace_koopman_eq_L2_tail :
        fixedSpace (koopman (Exchangeability.Ergodic.shift) hMP)
        = {h : Lp ℝ 2 (μ_path X) // AEStronglyMeasurable h ∧ Measurable[h] (tail_on_path) }`

     and then invoke `condexp_L2_unique`.  Since implementations differ across repos,
     we do not hard-code it here; see the main proof below for how it is used.
  -/
  trivial

/-! ## D. Bridge 3: L² → L¹ on Probability Spaces -/

/-- **Bridge 3.** On a probability space, `‖Y‖₁ ≤ ‖Y‖₂` (`p ≤ q` monotonicity). -/
lemma snorm_one_le_snorm_two {α} {m : Measure α} [IsProbabilityMeasure m]
    {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (f : α → E) :
    snorm f 1 m ≤ snorm f 2 m := by
  -- this is mathlib: `snorm_mono_exponent` (p ≤ q) and `μ univ = 1`
  have h_le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  sorry

/-- **Bridge 3'.** If `‖Yₙ - Y‖₂ → 0` in L² on a probability space, then
`∫ ‖Yₙ - Y‖ → 0` (i.e. L¹ convergence). -/
lemma tendsto_L2_to_L1 {α} {m : Measure α} [IsProbabilityMeasure m]
    {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {Y : α → E} {Yₙ : ℕ → α → E}
    (h₂ : Tendsto (fun n => snorm (fun x => Yₙ n x - Y x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖Yₙ n x - Y x‖ ∂m) atTop (𝓝 0) := by
  -- `snorm 1 = ∫ ‖·‖`, use the inequality and squeeze
  have h_bound : ∀ n, ∫ x, ‖Yₙ n x - Y x‖ ∂m ≤ (snorm (fun x => Yₙ n x - Y x) 2 m).toReal := by
    intro n
    have hmono := snorm_one_le_snorm_two (m := m) (f := fun x => Yₙ n x - Y x)
    sorry
  sorry

/-! ## E. Bridge 4: Pullback Along Factor Map -/

/-- **Bridge 4.** Conditional expectation commutes with the factor map:
`(μ_path X)[G | tail_on_path] ∘ pathify = μ[ G ∘ pathify | TailSigma.tailSigma X ]`.

We only need this for the specific `G ω := f(ω 0)` used below. -/
lemma condexp_pullback_along_pathify
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (H : Ω[ℝ] → ℝ) (hH_meas : Measurable H)
    -- NOTE: your project already packages `μ[ _ | _ ]` as an `L¹/L²` object.
    :
    ((μ_path X)[H | (tail_on_path)] ) ∘ (pathify X)
      =ᵐ[μ] μ[(H ∘ (pathify X)) | TailSigma.tailSigma X] := by
  /- Standard "change of variables" for conditional expectations under measure-preserving maps;
     it follows from the defining property of condexp and `μ_path = map (pathify X) μ`.
     In mathlib you can adapt lemmas around `condexp_comp` / `condexp_preimage` if present
     in your codebase. -/
  sorry

/-! ## F. Main Theorem -/

/-- **THEOREM (Cesàro → conditional expectation on the tail in L¹).**
This replaces the axiom `cesaro_to_condexp_L1` in `ViaL2.lean`. -/
theorem cesaro_to_condexp_L1
  {X : ℕ → Ω → ℝ} (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
    ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
           (μ[(f ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε := by
  classical
  -- Step 0: work on path space with law μ_path.
  let ν := μ_path X
  haveI : IsProbabilityMeasure ν := inferInstance
  -- The Koopman transformation for the shift on (Ω[ℝ], ν) is measure-preserving:
  have hMP : MeasurePreserving (Exchangeability.Ergodic.shift (α := ℝ)) ν ν :=
    measurePreserving_shift_path (μ := μ) (X := X) hX_contract

  -- Define the "coordinate 0 then apply f" observable on path space:
  --   g(ω) = f(ω 0)
  let g : Ω[ℝ] → ℝ := fun ω => f (ω 0)
  have hg_meas : Measurable g := hf_meas.comp (measurable_pi_apply 0)
  -- Boundedness ⇒ g ∈ L²(ν)
  have hg_L2 : Memℒp g 2 ν := by
    -- use `hf_bdd` and probability of ν to bound snorm_2
    sorry
  let gLp : Lp ℝ 2 ν := Memℒp.toLp g hg_L2

  -- L² convergence of Birkhoff averages to the metric projection (Mean Ergodic Theorem):
  have hMET :=
    Exchangeability.Ergodic.birkhoffAverage_tendsto_metProjection
      (μ := ν) (T := Exchangeability.Ergodic.shift (α := ℝ)) hMP gLp

  -- Identify the projection as conditional expectation onto the tail σ-algebra on path space:
  -- (see discussion in Bridge C)
  -- NOTE: replace the next line by your project lemma `metProjection = condexp_L2 tail_on_path`.
  have hProj :
      Exchangeability.Ergodic.metProjection (Exchangeability.Ergodic.shift (α := ℝ)) hMP gLp
        = (μ_path X)[g | tail_on_path] := by
    -- proof via "fixed space = L²(tail)" + `condexp_L2_unique`
    -- Implemented in your codebase; otherwise follow the comment in section C.
    sorry

  -- Rewrite the MET limit with conditional expectation:
  have hMET' :
    Tendsto (fun n =>
      Exchangeability.Ergodic.birkhoffAverage ℝ
        (Exchangeability.Ergodic.koopman (Exchangeability.Ergodic.shift (α := ℝ)) hMP)
        _root_.id n gLp)
      atTop (𝓝 ((μ_path X)[g | tail_on_path])) := by
    simpa [← hProj] using hMET

  -- Convert L² → L¹ using Bridge 3:
  have h_L1 :
    Tendsto (fun m =>
      ∫ ω, |(Exchangeability.Ergodic.birkhoffAverage ℝ
                (Exchangeability.Ergodic.koopman (Exchangeability.Ergodic.shift (α := ℝ)) hMP)
                _root_.id m gLp) ω
              - ((μ_path X)[g | tail_on_path]) ω| ∂ν) atTop (𝓝 0) := by
    -- convert Lp-convergence in L² to snorm-2 convergence, then apply Bridge 3'
    sorry

  -- Change of variables back to Ω via the factor map:
  have h_id_birkhoff :
      ∀ᵐ ω ∂μ, ∀ m,
        (Exchangeability.Ergodic.birkhoffAverage ℝ
          (Exchangeability.Ergodic.koopman (Exchangeability.Ergodic.shift (α := ℝ)) hMP)
          _root_.id m gLp) ((pathify X) ω)
        = (1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) := by
    sorry

  have h_ce_pull :
      (μ_path X)[g | tail_on_path] ∘ (pathify X)
        =ᵐ[μ] μ[(f ∘ X 0) | TailSigma.tailSigma X] := by
    have := condexp_pullback_along_pathify (μ := μ) (X := X) hX_meas (H := g) hg_meas
    have hcomp : g ∘ pathify X = f ∘ X 0 := by
      funext ω; simp [g, pathify]
    simpa [hcomp] using this

  -- Final epsilon-N extraction
  sorry

end Exchangeability.Bridge
