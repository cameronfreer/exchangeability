/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Kernel.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Tail.TailSigma
import Exchangeability.PathSpace.Shift
import Exchangeability.Probability.MeasureKernels

/-!
# Common Ending for de Finetti Proofs

This file contains the common final step shared by Kallenberg's First and Second proofs
of de Finetti's theorem. Both proofs construct a directing measure ν and then use
the same argument to establish the conditional i.i.d. property.

## The common structure

Given:
- A contractable/exchangeable sequence ξ
- A directing measure ν (constructed differently in each proof)
- The property that E[f(ξ_i) | ℱ] = ν^f for bounded measurable f

Show:
- ξ is conditionally i.i.d. given the tail σ-algebra

## Integration with Mathlib

This file uses several key mathlib components:
- `Measure.pi`: Finite product measures from `Mathlib.MeasureTheory.Constructions.Pi`
- `Kernel`: Probability kernels from `Mathlib.Probability.Kernel.Basic`
- `MeasureSpace.induction_on_inter`: π-λ theorem from `Mathlib.MeasureTheory.PiSystem`
- `Ergodic`, `MeasurePreserving`: From `Mathlib.Dynamics.Ergodic.Ergodic`
- `condExp`: Conditional expectation from
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`

See also `Exchangeability.ConditionallyIID` for the definition of conditionally i.i.d. sequences
using mathlib's measure theory infrastructure.

## References

* Kallenberg (2005), page 26-27: "The proof can now be completed as before"
* Kallenberg (2005), Chapter 10: Stationary Processes and Ergodic Theory (FMP 10.2-10.4)

-/

noncomputable section

namespace Exchangeability.DeFinetti.CommonEnding

open MeasureTheory ProbabilityTheory
open Exchangeability.PathSpace (shift shift_measurable IsShiftInvariant isShiftInvariant_iff)
open scoped BigOperators
open Set
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## Tail σ-algebras and Invariant σ-fields

For an exchangeable or contractable sequence X : ℕ → Ω → α, the **tail σ-algebra** consists
of events that depend only on the "tail" of the sequence, i.e., events invariant under
modifications of finitely many coordinates.

Following Kallenberg (FMP 10.2-10.4):
- A set I is **invariant** under a transformation T if T⁻¹I = I
- A set I is **almost invariant** if μ(I Δ T⁻¹I) = 0
- The collection of invariant sets forms the **invariant σ-field** ℐ
- The collection of almost invariant sets forms the **almost invariant σ-field** ℐ'
- **Key result (FMP 10.4)**: ℐ' = ℐ^μ (the μ-completion of ℐ)

For exchangeable sequences:
- The shift operator T: (ℕ → α) → (ℕ → α) by (Tξ)(n) = ξ(n+1) is the natural
  transformation
- The tail σ-algebra is related to the shift-invariant σ-field
- A function f is tail-measurable iff it's measurable w.r.t. the tail σ-algebra
- **FMP 10.3**: f is invariant/almost invariant iff f is ℐ-measurable/ℐ^μ-measurable

The directing measure ν constructed in de Finetti proofs is tail-measurable (almost invariant).
This is essential for showing that ν defines a proper conditional kernel.

Note: Formalizing tail σ-algebra equality with shift-invariant σ-field is future work.
-/

-- NOTE: shift operator, IsShiftInvariant, and related lemmas are imported from PathSpace.Shift
-- The shift operator (shift ξ) n = ξ (n + 1) is fundamental to studying exchangeable sequences
-- and is now defined in Exchangeability.PathSpace.Shift to avoid duplication across the codebase.

/-- The **invariant σ-field** ℐ consists of all measurable shift-invariant sets.
Following FMP 10.2, this forms a σ-field. -/
def invariantSigmaField (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.comap shift inferInstance

/-- A measure on the path space is **almost shift-invariant** on a set S if
μ(S ∆ shift⁻¹(S)) = 0 (symmetric difference). This is the analogue of FMP 10.2's
almost invariance. -/
def IsAlmostShiftInvariant {α : Type*} [MeasurableSpace α]
    (μ : Measure (ℕ → α)) (S : Set (ℕ → α)) : Prop :=
  μ ((S \ (shift ⁻¹' S)) ∪ ((shift ⁻¹' S) \ S)) = 0

/-- The **tail σ-algebra** for infinite sequences consists of events that are
"asymptotically independent" of the first n coordinates for all n.

Now using the canonical definition from `Exchangeability.Tail.tailShift`,
defined as `⨅ n, comap (shift^n) inferInstance`.

For exchangeable sequences, this equals the shift-invariant σ-field
(to be proven using FMP 10.3-10.4). -/
def tailSigmaAlgebra (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  Exchangeability.Tail.tailShift α

/-- A function on the path space is **tail-measurable** if it's measurable with respect
to the tail σ-algebra. By FMP 10.3, this is equivalent to being (almost) shift-invariant. -/
def IsTailMeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (ℕ → α) → β) : Prop :=
  @Measurable (ℕ → α) β (tailSigmaAlgebra α) _ f

/-- For a probability measure μ on path space, a function is **almost tail-measurable**
if it differs from a tail-measurable function on a μ-null set.
By FMP 10.4, this is equivalent to measurability w.r.t. the μ-completion of the invariant σ-field.

Note: A more complete formalization would use measure completion. -/
def IsAlmostTailMeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (ℕ → α)) (f : (ℕ → α) → β) : Prop :=
  ∃ g : (ℕ → α) → β, IsTailMeasurable g ∧ f =ᵐ[μ] g

/-!
## Helper lemmas for product measures

These lemmas establish the connection between bounded functions and indicator functions,
which is essential for the monotone class argument.
-/

/-- Indicator functions are bounded. This is a trivial but useful fact for the
monotone class extension. -/
lemma indicator_bounded {α : Type*} {s : Set α} :
    ∃ M : ℝ, ∀ x, |s.indicator (fun _ => (1 : ℝ)) x| ≤ M := by
  refine ⟨1, ?_⟩
  intro x
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The ENNReal value of an indicator function is either 0 or 1. -/
lemma indicator_mem_zero_one {α : Type*} {s : Set α} {x : α} :
    ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ∈ ({0, 1} : Set ENNReal) := by
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h, ENNReal.ofReal_one]
  · simp [Set.indicator_of_notMem h, ENNReal.ofReal_zero]

/-- The ENNReal value of an indicator function is at most 1. -/
lemma indicator_le_one {α : Type*} {s : Set α} {x : α} :
    ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ≤ 1 := by
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h, ENNReal.ofReal_one]
  · simp [Set.indicator_of_notMem h, ENNReal.ofReal_zero]

/-- A product of ENNReal values equals 0 iff at least one factor is 0. -/
lemma prod_eq_zero_iff {ι : Type*} [Fintype ι] {f : ι → ENNReal} :
    ∏ i, f i = 0 ↔ ∃ i, f i = 0 := by
  constructor
  · intro h
    by_contra h_all_nonzero
    push_neg at h_all_nonzero
    have : ∀ i, f i ≠ 0 := h_all_nonzero
    have prod_ne_zero : ∏ i, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => this i
    exact prod_ne_zero h
  · intro ⟨i, hi⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact hi

/-- For values in {0, 1}, the product equals 1 iff all factors equal 1. -/
lemma prod_eq_one_iff_of_zero_one {ι : Type*} [Fintype ι] {f : ι → ENNReal}
    (hf : ∀ i, f i ∈ ({0, 1} : Set ENNReal)) :
    ∏ i, f i = 1 ↔ ∀ i, f i = 1 := by
  constructor
  · intro h i
    have mem := hf i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mem
    rcases mem with h0 | h1
    · exfalso
      simp [Finset.prod_eq_zero (Finset.mem_univ i) h0] at h
    · exact h1
  · intro h; simp [h]

/-- The product of finitely many terms, each bounded by 1, is bounded by 1.
This is useful for products of indicator functions. -/
lemma prod_le_one_of_le_one {ι : Type*} [Fintype ι] {f : ι → ENNReal}
    (hf : ∀ i, f i ≤ 1) : ∏ i, f i ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _
    exact zero_le _
  · intro i _
    exact hf i

-- Note: measurable_prod_ennreal has been moved to Exchangeability.Probability.MeasureKernels

/-- The ENNReal indicator function composed with a measurable function is measurable. -/
lemma measurable_indicator_comp {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (hf : Measurable f) (s : Set α) (hs : MeasurableSet s) :
    Measurable fun ω => ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) (f ω)) := by
  -- The indicator function is measurable when composed with a measurable function
  have : Measurable fun ω => s.indicator (fun _ => (1 : ℝ)) (f ω) := by
    fun_prop (disch := measurability)
  exact ENNReal.measurable_ofReal.comp this

/-- The product of bounded functions is bounded.

Uses mathlib's `Finset.prod_le_prod` to bound product by product of bounds. -/
lemma product_bounded {ι : Type*} [Fintype ι] {α : Type*}
    (f : ι → α → ℝ) (hf : ∀ i, ∃ M, ∀ x, |f i x| ≤ M) :
    ∃ M, ∀ x, |∏ i, f i x| ≤ M := by
  classical
  -- pointwise bounds
  choose M hM using hf
  -- pick bounds ≥ 1 to keep nonnegativity of products
  let M' : ι → ℝ := fun i => max (M i) 1
  have hM' : ∀ i x, |f i x| ≤ M' i := by
    intro i x; exact (hM i x).trans (le_max_left _ _)
  have hM'_nonneg : ∀ i, 0 ≤ M' i :=
    fun i => zero_le_one.trans (le_max_right _ _)
  -- Key inductive claim
  have key : ∀ (s : Finset ι) (x : α), |s.prod (fun i => f i x)| ≤ s.prod M' := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      calc |Finset.prod (insert a s) (fun i => f i x)|
          = |(f a x) * s.prod (fun i => f i x)| := by rw [Finset.prod_insert ha]
        _ = |f a x| * |s.prod (fun i => f i x)| := by rw [abs_mul]
        _ ≤ M' a * |s.prod (fun i => f i x)| :=
            mul_le_mul_of_nonneg_right (hM' a x) (abs_nonneg _)
        _ ≤ M' a * s.prod M' :=
            mul_le_mul_of_nonneg_left ih (hM'_nonneg a)
        _ = Finset.prod (insert a s) M' := by rw [Finset.prod_insert ha]
  refine ⟨Finset.univ.prod M', ?_⟩
  intro x
  simpa using key Finset.univ x


/- ### Key Bridge Lemma
If `E[f(Xᵢ) | tail] = ∫ f dν` for all bounded measurable `f`, then for indicator functions
we get `E[𝟙_B(Xᵢ) | tail] = ν(B)`.  This intuition underlies the hypothesis `h_bridge` used
below.
-/

/-- For conditionally i.i.d. sequences, the joint distribution of finitely many coordinates
equals the average of the product measures built from the directing measure.

This is an intermediate result showing how the finite-dimensional distributions are determined
by the directing measure `ν`.

Note: We use lintegral (∫⁻) for measure-valued integrals since measures are `ENNReal`-valued.

Proof strategy:
1. Postulate the bridging identity `h_bridge` for indicators: the integral of the
   product of coordinate indicators equals the integral of the product of the
   conditional marginals
2. Interpret the indicator product as the indicator of the event and rewrite the
   right-hand side using product measures
4. The LHS is `μ {ω | ∀ i, Xᵢ(ω) ∈ Bᵢ}`; the RHS is the integral of the product measure
5. From these, we obtain the desired equality on rectangles

The missing ingredient is the `h_bridge` identity, which is supplied later from the
directing-measure construction.
-/

-- Product of {0,1}-valued indicator functions equals indicator of intersection
private lemma prod_indicators_eq_indicator_intersection {Ω α : Type*} {m : ℕ} (X : ℕ → Ω → α)
    (k : Fin m → ℕ) (B : Fin m → Set α) :
    (fun ω : Ω => ∏ i : Fin m,
      ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)))
      = Set.indicator {ω | ∀ i : Fin m, X (k i) ω ∈ B i} (fun _ => 1) := by
  classical
  set E := {ω | ∀ i : Fin m, X (k i) ω ∈ B i}
  funext ω
  by_cases hω : ω ∈ E
  · -- Case: ω ∈ E, all indicators are 1, product is 1
    have h1 : ∀ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) = 1 := by
      intro i
      have Hi : X (k i) ω ∈ B i := by simpa [E] using (hω i)
      simp [Set.indicator_of_mem Hi]
    have : ∀ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) = 1 := by
      intro i; simp [h1 i]
    have hprod :
        ∏ i : Fin m,
            ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) = 1 := by
      simp [this]
    rw [Set.indicator_of_mem hω, hprod]
  · -- Case: ω ∉ E, some indicator is 0, product is 0
    have hzero : ∃ j : Fin m,
        ENNReal.ofReal ((B j).indicator (fun _ => (1 : ℝ)) (X (k j) ω)) = 0 := by
      have : ¬∀ i : Fin m, X (k i) ω ∈ B i := by simpa [E] using hω
      rcases not_forall.mp this with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      simp [Set.indicator, hj]
    rcases hzero with ⟨j, hj⟩
    have hjmem : (j : Fin m) ∈ (Finset.univ : Finset (Fin m)) := by simp
    have hprod :
        ∏ i : Fin m,
            ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) = 0 :=
      Finset.prod_eq_zero hjmem hj
    simpa [Set.indicator, hω, hprod]

-- Measure of a set equals lintegral of its indicator function
private lemma measure_via_indicator_integral (μ : Measure Ω) (X : ℕ → Ω → α)
    (hX_meas : ∀ i, Measurable (X i)) (m : ℕ) (k : Fin m → ℕ)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    μ {ω | ∀ i, X (k i) ω ∈ B i}
      = ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ := by
  classical
  set E := {ω | ∀ i : Fin m, X (k i) ω ∈ B i}
  have hEvtMeas : MeasurableSet E := by
    have : E = ⋂ i : Fin m, {ω | X (k i) ω ∈ B i} := by ext ω; simp [E]
    simpa [this] using MeasurableSet.iInter fun i => (hX_meas (k i)) (hB i)
  have hProdEqIndicator := @prod_indicators_eq_indicator_intersection Ω α m X k B
  have hlin := lintegral_indicator (μ := μ) (s := E) (f := fun _ => 1) hEvtMeas
  have hconst := lintegral_const (μ := μ.restrict E) (c := 1)
  have hconst' : ∫⁻ ω, 1 ∂μ.restrict E = μ E := by
    simp [Measure.restrict_apply, hconst]
  have hμE : μ E = ∫⁻ ω, E.indicator (fun _ => 1) ω ∂μ := by
    simpa [hconst'] using hlin.symm
  rw [hμE, ← hProdEqIndicator]

-- Product of measures on rectangles equals Measure.pi evaluation
private lemma product_measure_on_rectangle {Ω α : Type*} [MeasurableSpace α]
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω)) (m : ℕ)
    (B : Fin m → Set α) (ω : Ω) :
    ∏ i : Fin m, ν ω (B i)
      = (Measure.pi fun _i : Fin m => ν ω) {x : Fin m → α | ∀ i, x i ∈ B i} := by
  haveI : IsProbabilityMeasure (ν ω) := hν_prob ω
  have set_eq : {x : Fin m → α | ∀ i, x i ∈ B i} = Set.univ.pi fun i => B i := by
    ext x; simp [Set.pi]
  rw [set_eq, Measure.pi_pi]

lemma fidi_eq_avg_product {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (_hν_meas : ∀ s, MeasurableSet s → Measurable (fun ω => ν ω s))
    (m : ℕ) (k : Fin m → ℕ) (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i))
    (h_bridge :
      ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
        = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ) :
    μ {ω | ∀ i, X (k i) ω ∈ B i} =
      ∫⁻ ω, (Measure.pi fun _ : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := by
  -- LHS: Convert measure to integral of indicator product (via helper)
  have lhs_eq := measure_via_indicator_integral μ X hX_meas m k B hB

  -- RHS: Convert product of measures to Measure.pi form (via helper)
  have rhs_eq : ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ
      = ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := by
    congr 1
    funext ω
    exact product_measure_on_rectangle ν hν_prob m B ω

  -- Chain the equalities: μ E = integral of indicators = integral of products = integral of pi
  calc μ {ω | ∀ i, X (k i) ω ∈ B i}
      = ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ := lhs_eq
    _ = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := h_bridge
    _ = ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := rhs_eq

-- Note: rectangles_isPiSystem has been moved to Exchangeability.Probability.MeasureKernels

-- Note: rectangles_generate_pi_sigma has been moved to Exchangeability.Probability.MeasureKernels

/-- Pushforward of a measure through coordinate selection equals the marginal distribution.
This connects the map in the ConditionallyIID definition to the probability of events.

This is a direct application of `Measure.map_apply` from mathlib. -/
lemma map_coords_apply {μ : Measure Ω} (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (m : ℕ) (k : Fin m → ℕ) (B : Set (Fin m → α)) (hB : MeasurableSet B) :
    (Measure.map (fun ω i => X (k i) ω) μ) B = μ {ω | (fun i => X (k i) ω) ∈ B} := by
  -- The function (fun ω i => X (k i) ω) is measurable as a composition of measurable functions
  have h_meas : Measurable (fun ω i => X (k i) ω) := by
    -- Use measurable_pi_iff: a function to a pi type is measurable iff each component is
    rw [measurable_pi_iff]
    intro i
    exact hX_meas (k i)
  -- Apply Measure.map_apply
  rw [Measure.map_apply h_meas hB]
  -- The preimage is definitionally equal to the set we want
  rfl

-- Note: aemeasurable_measure_pi has been moved to Exchangeability.Probability.MeasureKernels

/-- The bind of a probability measure with the product measure kernel equals the integral
of the product measure. This is the other side of the ConditionallyIID equation.

Note: We use lintegral (∫⁻) for measure-valued integrals since measures are ENNReal-valued.

This is a direct application of `Measure.bind_apply` from mathlib's Giry monad. -/
lemma bind_pi_apply {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, MeasurableSet s → Measurable (fun ω => ν ω s))
    (m : ℕ) (B : Set (Fin m → α)) (hB : MeasurableSet B) :
    (μ.bind fun ω => Measure.pi fun _ : Fin m => ν ω) B =
      ∫⁻ ω, (Measure.pi fun _ : Fin m => ν ω) B ∂μ := by
  -- The kernel (fun ω => Measure.pi fun _ => ν ω) is AE-measurable by our helper lemma
  have h_ae_meas : AEMeasurable (fun ω => Measure.pi fun _ : Fin m => ν ω) μ :=
    aemeasurable_measure_pi ν hν_prob hν_meas
  -- Now apply Measure.bind_apply from mathlib's Giry monad
  exact Measure.bind_apply hB h_ae_meas

/-- Two finite measures are equal if they agree on a π-system that generates the σ-algebra.
This is the key uniqueness result from Dynkin's π-λ theorem.

This is mathlib's `Measure.ext_of_generate_finite` from
`Mathlib.MeasureTheory.Measure.Typeclasses.Finite`. -/
lemma measure_eq_of_agree_on_pi_system {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (C : Set (Set Ω)) (hC_pi : IsPiSystem C)
    (hC_gen : ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom C)
    (h_agree : ∀ s ∈ C, μ s = ν s) :
    μ = ν := by
  -- For probability measures, μ univ = ν univ = 1
  have h_univ : μ Set.univ = ν Set.univ := by
    by_cases h : Set.univ ∈ C
    · exact h_agree Set.univ h
    · -- Both are probability measures, so both measure univ as 1
      simp [measure_univ]
  exact ext_of_generate_finite C hC_gen hC_pi h_agree h_univ

/-!
## The common completion argument

Kallenberg's text says: "The proof can now be completed as before."

This refers to the final step of the first proof, which goes:
1. Have directing measure ν with E[f(ξ_i) | ℱ] = ν^f
2. Use monotone class argument to extend to product sets
3. Show P[∩ Bᵢ | ℱ] = ν^k B for B ∈ 𝒮^k

### Proof Strategy Overview

The key insight is to connect three equivalent characterizations of conditional i.i.d.:

**A. Bounded Functions** (what we have from ergodic theory):
   For all bounded measurable f and all i:
   E[f(Xᵢ) | tail] = ∫ f d(ν ω) almost everywhere

**B. Indicator Functions** (intermediate step):
   For all measurable sets B and all i:
   E[𝟙_B(Xᵢ) | tail] = ν(B) almost everywhere

**C. Product Sets** (what we need for ConditionallyIID):
   For all m, k, and measurable rectangles B₀ × ... × Bₘ₋₁:
   μ{ω : ∀ i < m, X_{kᵢ}(ω) ∈ Bᵢ} = ∫ ∏ᵢ ν(Bᵢ) dμ

The progression:
- **A → B**: Apply A to indicator functions (they're bounded)
- **B → C**: Use product structure and independence
  - ∏ᵢ 𝟙_{Bᵢ}(Xᵢ) = 𝟙_{B₀×...×Bₘ₋₁}(X₀,...,Xₘ₋₁)
  - E[∏ᵢ 𝟙_{Bᵢ}(Xᵢ)] = ∏ᵢ E[𝟙_{Bᵢ}(Xᵢ)] = ∏ᵢ ν(Bᵢ)
    (conditional independence!)
- **C → ConditionallyIID**: π-λ theorem
  - Rectangles form a π-system generating the product σ-algebra
  - Both `Measure.map` and `μ.bind (Measure.pi ν)` agree on rectangles
  - By uniqueness of measure extension, they're equal everywhere

This modular structure makes each step verifiable and connects to standard measure theory results.
-/

/-- Given a sequence and a directing measure satisfying the key property
`E[f (ξᵢ) ∣ ℱ] = ν^f` for bounded measurable functions, we can establish
conditional independence.

This is the "completed As before" step referenced in the Second proof.

Outline (to be implemented):

  • **From directing measure to conditional kernels**: build the kernel
    `K : Kernel Ω α` given by `ω ↦ ν ω`, verifying tail measurability using
    FMP 10.3/10.4 (almost invariant σ-fields).
  • **Recover conditional i.i.d.**: for bounded measurable `f`, use the
    hypothesis to show that `E[f (Xᵢ) ∣ tail] = ∫ f d(K ω)`.
  • **Invoke `exchangeable_of_conditionallyIID`** (see
    `Exchangeability/ConditionallyIID.lean`) once the `conditionallyIID` record
    is built from `K`. That lemma already yields exchangeability; combining it
    with the converse direction gives conditional independence.
  • **Monotone class / π-λ argument**: extend equality from bounded measurable
    functions to cylinder sets, finishing the conditional independence proof.

The implementation will mirror Kallenberg's argument but reframed so this common
lemma serves both the Koopman and L² approaches.
-/
-- Pushforward of probability measure via coordinate map is probability
private lemma map_coords_isProbabilityMeasure {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) (m : ℕ) (k : Fin m → ℕ) :
    IsProbabilityMeasure (Measure.map (fun ω i => X (k i) ω) μ) := by
  have h_meas : Measurable (fun ω i => X (k i) ω) := by
    rw [measurable_pi_iff]
    intro i
    exact hX_meas (k i)
  exact Measure.isProbabilityMeasure_map h_meas.aemeasurable

-- Product of probability measures is a probability measure
private lemma pi_of_prob_is_prob {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω)) (m : ℕ) :
    ∀ ω, IsProbabilityMeasure (Measure.pi fun _ : Fin m => ν ω) := by
  intro ω
  constructor
  have h : (Set.univ : Set (Fin m → α)) = Set.univ.pi (fun (_ : Fin m) => Set.univ) := by
    ext x; simp
  rw [h, Measure.pi_pi]
  simp [measure_univ]

-- Bind of probability measure with probability kernels is probability
private lemma bind_pi_isProbabilityMeasure {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, MeasurableSet s → Measurable (fun ω => ν ω s)) (m : ℕ) :
    IsProbabilityMeasure (μ.bind fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  constructor
  have h_ae_meas : AEMeasurable (fun ω => Measure.pi fun _ : Fin m => ν ω) μ :=
    aemeasurable_measure_pi ν hν_prob hν_meas
  rw [Measure.bind_apply .univ h_ae_meas]
  simp [measure_univ]

-- Convert rectangle notation and prove measurability
private lemma rectangle_as_pi_measurable (m : ℕ) (B : Fin m → Set α)
    (hB_meas : ∀ i, MeasurableSet (B i)) :
    MeasurableSet {x : Fin m → α | ∀ i, x i ∈ B i} := by
  have : {x : Fin m → α | ∀ i, x i ∈ B i} = Set.univ.pi fun i => B i := by
    ext x; simp [Set.pi]
  rw [this]
  exact MeasurableSet.univ_pi hB_meas

theorem conditional_iid_from_directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, MeasurableSet s → Measurable (fun ω => ν ω s))
    (h_bridge : ∀ {m : ℕ} (k : Fin m → ℕ), Function.Injective k → ∀ (B : Fin m → Set α),
      (∀ i, MeasurableSet (B i)) →
        ∫⁻ ω, ∏ i : Fin m,
            ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
          = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ) :
    ConditionallyIID μ X := by
      -- Proof roadmap following Kallenberg's argument:
      --
      -- STEP 1: Package ν as satisfying the ConditionallyIID definition
      -- The definition requires: ∃ ν, (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      --   (∀ B, MeasurableSet B → Measurable (fun ω => ν ω B)) ∧
      --   ∀ m k, StrictMono k → Measure.map (fun ω i => X (k i) ω) μ =
      --     μ.bind (fun ω => Measure.pi fun _ => ν ω)
      use ν, hν_prob, hν_meas

      intro m k hk_strict  -- hk_strict : StrictMono k gives injectivity for h_bridge

      -- STEP 2: Show the finite-dimensional distributions match
      -- Need: Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      --     = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)
      --
      -- Strategy: Use measure_eq_of_agree_on_pi_system with rectangles as the π-system

      -- Define the two measures we want to prove equal
      let μ_map := Measure.map (fun ω i => X (k i) ω) μ
      let μ_bind := μ.bind fun ω => Measure.pi fun _ : Fin m => ν ω

      -- Both are probability measures (via helpers)
      have h_map_prob : IsProbabilityMeasure μ_map :=
        map_coords_isProbabilityMeasure X hX_meas m k

      have h_bind_prob : IsProbabilityMeasure μ_bind :=
        bind_pi_isProbabilityMeasure ν hν_prob hν_meas m

      -- Define the π-system of measurable rectangles
      let C : Set (Set (Fin m → α)) := {S | ∃ (B : Fin m → Set α),
        (∀ i, MeasurableSet (B i)) ∧ S = {x | ∀ i, x i ∈ B i}}

      -- Show C is a π-system (already proved)
      have hC_pi : IsPiSystem C := rectangles_isPiSystem

      -- Show C generates the product σ-algebra (already proved)
      have hC_gen : (inferInstance : MeasurableSpace (Fin m → α)) =
          MeasurableSpace.generateFrom C := rectangles_generate_pi_sigma

      -- Apply measure_eq_of_agree_on_pi_system
      apply measure_eq_of_agree_on_pi_system μ_map μ_bind C hC_pi hC_gen

      -- Show both measures agree on rectangles
      intro S hS
      -- S is a rectangle, so S = {x | ∀ i, x i ∈ B i} for some B
      obtain ⟨B, hB_meas, rfl⟩ := hS

      -- LHS: μ_map {x | ∀ i, x i ∈ B i}
      have lhs_eq : μ_map {x | ∀ i, x i ∈ B i} = μ {ω | ∀ i, X (k i) ω ∈ B i} := by
        have hB := rectangle_as_pi_measurable m B hB_meas
        exact map_coords_apply X hX_meas m k _ hB

      -- RHS: μ_bind {x | ∀ i, x i ∈ B i}
      have rhs_eq : μ_bind {x | ∀ i, x i ∈ B i} =
          ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := by
        have hB := rectangle_as_pi_measurable m B hB_meas
        exact bind_pi_apply ν hν_prob hν_meas m _ hB

      -- Both equal by fidi_eq_avg_product
      rw [lhs_eq, rhs_eq]

      -- Apply fidi_eq_avg_product using the bridging hypothesis
      exact fidi_eq_avg_product X hX_meas ν hν_prob hν_meas m k B hB_meas
        (h_bridge (k := k) hk_strict.injective (B := B) hB_meas)

/-- **FMP 1.1: Monotone Class Theorem (Sierpiński)** = Dynkin's π-λ theorem.

Let 𝒞 be a π-system and 𝒟 a λ-system in some space Ω such that 𝒞 ⊆ 𝒟.
Then σ(𝒞) ⊆ 𝒟.

**Proof outline** (Kallenberg):
1. Assume 𝒟 = λ(𝒞) (smallest λ-system containing 𝒞)
2. Show 𝒟 is a π-system (then it's a σ-field)
3. Two-step extension:
   - Fix B ∈ 𝒞, define 𝒜_B = {A : A ∩ B ∈ 𝒟}, show 𝒜_B is λ-system ⊇ 𝒞
   - Fix A ∈ 𝒟, define ℬ_A = {B : A ∩ B ∈ 𝒟}, show ℬ_A is λ-system ⊇ 𝒞

**Mathlib version**: `MeasurableSpace.induction_on_inter`

Mathlib's version is stated as an induction principle: if a predicate C holds on:
- The empty set
- All sets in the π-system 𝒞
- Is closed under complements
- Is closed under countable disjoint unions

Then C holds on all measurable sets in σ(𝒞).

**Definitions in mathlib**:
- `IsPiSystem`: A collection closed under binary non-empty intersections
  (Mathlib/MeasureTheory/PiSystem.lean)
- `DynkinSystem`: A structure containing ∅, closed under complements and
  countable disjoint unions (Mathlib/MeasureTheory/PiSystem.lean)
- `induction_on_inter`: The π-λ theorem as an induction principle
  (Mathlib/MeasureTheory/PiSystem.lean)

This theorem is now a direct wrapper around mathlib's `induction_on_inter`.
-/
theorem monotone_class_theorem
    {Ω' : Type*} {m : MeasurableSpace Ω'} {C : ∀ s : Set Ω', MeasurableSet s → Prop}
    {s : Set (Set Ω')} (h_eq : m = MeasurableSpace.generateFrom s)
    (h_inter : IsPiSystem s)
    (empty : C ∅ .empty)
    (basic : ∀ t (ht : t ∈ s), C t <| h_eq ▸ .basic t ht)
    (compl : ∀ t (htm : MeasurableSet t), C t htm → C tᶜ htm.compl)
    (iUnion : ∀ f : ℕ → Set Ω', Pairwise (fun i j => Disjoint (f i) (f j)) →
      ∀ (hf : ∀ i, MeasurableSet (f i)), (∀ i, C (f i) (hf i)) →
        C (⋃ i, f i) (MeasurableSet.iUnion hf))
    {t : Set Ω'} (htm : MeasurableSet t) :
    C t htm := by
  -- Direct application of mathlib's π-λ theorem (induction_on_inter)
  exact MeasurableSpace.induction_on_inter h_eq h_inter empty basic compl iUnion t htm

-- *Monotone-class remark.*  Earlier drafts included an explicit monotone-class lemma
-- (`monotone_class_product_extension`) proving the π-λ step described above.  The sole
-- remaining use of that lemma is captured abstractly by the `h_bridge` hypothesis, so the
-- sketch is retained only as commentary.
/-- Package the common ending as a reusable theorem.

Given a contractable sequence and a directing measure ν constructed via
either approach (Mean Ergodic Theorem or L² bound), this completes the
proof to conditional i.i.d.

This encapsulates the "completed as before" step.
-/
theorem complete_from_directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (_hX_contract : Contractable μ X)
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, MeasurableSet s → Measurable (fun ω => ν ω s))
    (h_bridge : ∀ {m : ℕ} (k : Fin m → ℕ), Function.Injective k → ∀ (B : Fin m → Set α),
      (∀ i, MeasurableSet (B i)) →
        ∫⁻ ω, ∏ i : Fin m,
            ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
          = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ) :
    ConditionallyIID μ X := by
  -- Use the skeleton lemma (to be completed later) to produce ConditionallyIID
  exact conditional_iid_from_directing_measure X hX_meas ν hν_prob hν_meas h_bridge

-- Summary and next steps for the common ending are recorded in the project notes.

end Exchangeability.DeFinetti.CommonEnding
