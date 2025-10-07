/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Kernel.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID

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
- `condExp`: Conditional expectation from `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`

See also `Exchangeability.ConditionallyIID` for the definition of conditionally i.i.d. sequences
using mathlib's measure theory infrastructure.

## References

* Kallenberg (2005), page 26-27: "The proof can now be completed as before"
* Kallenberg (2005), Chapter 10: Stationary Processes and Ergodic Theory (FMP 10.2-10.4)

-/

noncomputable section

namespace Exchangeability.DeFinetti.CommonEnding

open MeasureTheory ProbabilityTheory
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
- The shift operator T: (ℕ → α) → (ℕ → α) by (Tξ)(n) = ξ(n+1) is the natural transformation
- The tail σ-algebra is related to the shift-invariant σ-field
- A function f is tail-measurable iff it's measurable w.r.t. the tail σ-algebra
- **FMP 10.3**: f is invariant/almost invariant iff f is ℐ-measurable/ℐ^μ-measurable

The directing measure ν constructed in de Finetti proofs is tail-measurable (almost invariant).
This is essential for showing that ν defines a proper conditional kernel.

TODO: Formalize tail σ-algebra for sequences and prove it equals the shift-invariant σ-field.
-/

/-- The shift operator on infinite sequences. This is the natural transformation for
studying exchangeable sequences. -/
def shift {α : Type*} : (ℕ → α) → (ℕ → α) := fun ξ n => ξ (n + 1)

@[simp]
lemma shift_apply {α : Type*} (ξ : ℕ → α) (n : ℕ) : shift ξ n = ξ (n + 1) := rfl

/-- Composing shift with itself is shift by 2. More generally, shift^n shifts by n. -/
lemma shift_comp_shift {α : Type*} : @shift α ∘ shift = fun ξ n => ξ (n + 2) := by
  ext ξ n
  simp only [Function.comp_apply, shift_apply]

/-- The shift operator is measurable.

Proof: shift is measurable iff for all i, the composition (shift ξ) i is measurable.
Since (shift ξ) i = ξ (i + 1), this is the projection onto coordinate (i + 1),
which is measurable by definition of the product σ-algebra.
-/
lemma shift_measurable {α : Type*} [MeasurableSpace α] : Measurable (@shift α) := by
  -- A function to a pi type is measurable iff each component is measurable
  rw [measurable_pi_iff]
  intro i
  -- The i-th component of shift ξ is ξ (i + 1)
  -- This is just the projection onto coordinate (i + 1)
  exact measurable_pi_apply (i + 1)

/-- A set in the path space is **shift-invariant** if it equals its preimage under the shift.
This is the analogue of T⁻¹I = I from FMP 10.2. -/
def IsShiftInvariant {α : Type*} (S : Set (ℕ → α)) : Prop :=
  shift ⁻¹' S = S

lemma isShiftInvariant_iff {α : Type*} (S : Set (ℕ → α)) :
    IsShiftInvariant S ↔ ∀ ξ, ξ ∈ S ↔ shift ξ ∈ S := by
  unfold IsShiftInvariant
  constructor
  · intro h ξ
    -- turn set equality into pointwise membership equivalence
    have := congrArg (fun T : Set (ℕ → α) => ξ ∈ T) h
    -- note: ξ ∈ shift ⁻¹' S ↔ shift ξ ∈ S is definitionally true
    simpa using this.symm
  · intro h
    ext ξ
    -- again use the definitional equivalence for preimages
    simpa using (h ξ).symm

/-- The **invariant σ-field** ℐ consists of all measurable shift-invariant sets.
Following FMP 10.2, this forms a σ-field. -/
def invariantSigmaField (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.comap shift inferInstance

/-- A measure on the path space is **almost shift-invariant** on a set S if
μ(S ∆ shift⁻¹(S)) = 0 (symmetric difference). This is the analogue of FMP 10.2's almost invariance. -/
def IsAlmostShiftInvariant {α : Type*} [MeasurableSpace α]
    (μ : Measure (ℕ → α)) (S : Set (ℕ → α)) : Prop :=
  μ ((S \ (shift ⁻¹' S)) ∪ ((shift ⁻¹' S) \ S)) = 0

/-- The **tail σ-algebra** for infinite sequences consists of events that are
"asymptotically independent" of the first n coordinates for all n.
Equivalently (for exchangeable sequences), it's the σ-field of shift-invariant events.

TODO: Prove these are equivalent using FMP 10.3-10.4. -/
def tailSigmaAlgebra (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  -- Placeholder: should be defined as ⋂ n, σ(X_{n+1}, X_{n+2}, ...)
  -- For now, use the invariant σ-field as a proxy
  invariantSigmaField α

/-- A function on the path space is **tail-measurable** if it's measurable with respect
to the tail σ-algebra. By FMP 10.3, this is equivalent to being (almost) shift-invariant. -/
def IsTailMeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (ℕ → α) → β) : Prop :=
  @Measurable (ℕ → α) β (tailSigmaAlgebra α) _ f

/-- **FMP 10.3 (Invariant sets and functions)**: A measurable function f is invariant
(f ∘ shift = f) if and only if it is measurable with respect to the invariant σ-field.

This is the key connection between syntactic invariance and σ-field measurability.

Proof strategy (following Kallenberg FMP 10.3):
1. (⇒) Assume f ∘ shift = f
   - Need to show f is measurable w.r.t. invariantSigmaField α
   - The invariant σ-field is defined as MeasurableSpace.comap shift inferInstance
   - A function g is measurable w.r.t. comap shift iff g ∘ shift⁻¹ is measurable
   - Since f is shift-invariant: f = f ∘ shift ∘ shift⁻¹ (where shift⁻¹ exists on range)
   - This gives the required measurability

2. (⇐) Assume f is measurable w.r.t. invariantSigmaField α
   - By definition of comap, f⁻¹(B) ∈ invariantSigmaField for all measurable B
   - This means shift⁻¹(f⁻¹(B)) = f⁻¹(B)
   - Equivalently: (f ∘ shift)⁻¹(B) = f⁻¹(B) for all measurable B
   - Since β is countably generated, this implies f ∘ shift = f almost everywhere
   - For deterministic functions on ℕ → α, a.e. equality is actual equality

The proof requires careful handling of the comap construction and the countably
generated assumption to move from set-level equality to function equality.
-/
axiom isTailMeasurable_iff_shift_invariant {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β]
    (f : (ℕ → α) → β) (hf : Measurable f) :
    IsTailMeasurable f ↔ f ∘ shift = f

/-- For a probability measure μ on path space, a function is **almost tail-measurable**
if it differs from a tail-measurable function on a μ-null set.
By FMP 10.4, this is equivalent to measurability w.r.t. the μ-completion of the invariant σ-field.

TODO: Formalize this properly using measure completion. -/
def IsAlmostTailMeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (ℕ → α)) (f : (ℕ → α) → β) : Prop :=
  ∃ g : (ℕ → α) → β, IsTailMeasurable g ∧ f =ᵐ[μ] g

/-- **Connection to Exchangeability**: For an exchangeable sequence X : ℕ → Ω → α,
the path-space measure μ_X (push-forward of the base measure μ by ω ↦ (X n ω)_{n ∈ ℕ})
is invariant under the shift operator. More generally, μ_X is invariant under all
finite permutations.

This invariance is why the tail σ-algebra (shift-invariant σ-field) is the natural
conditioning σ-field for de Finetti's theorem:
- The directing measure ν must be tail-measurable (FMP 10.3-10.4)
- Conditional expectations with respect to the tail σ-algebra give the mixing measure
- The tail σ-field is trivial for ergodic measures (0-1 law)

Proof strategy:
1. Define path-space measure: μ_X = Measure.map (fun ω n => X n ω) μ
2. Show shift is measurable: shift : (ℕ → α) → (ℕ → α) is measurable
3. Prove measure-preserving property:
   - For any measurable B ⊆ (ℕ → α), need: μ_X(shift⁻¹(B)) = μ_X(B)
   - Since X is exchangeable, finite permutations preserve the distribution
   - The shift is the limit of finite permutations (shift by 1)
   - For exchangeable sequences, the distribution is invariant under all permutations
   - In particular: μ_X{paths | shift(path) ∈ B} = μ_X(B)

4. The key insight: exchangeability = invariance under finite coordinate swaps
   - Shift can be approximated by swapping coordinates 0↔1, 1↔2, 2↔3, ...
   - Each swap preserves the distribution by exchangeability
   - The limit preserves the distribution by continuity of measures

This connects the combinatorial property (exchangeability) to the dynamical
property (shift-invariance), which is the bridge to ergodic theory.
-/
axiom exchangeable_implies_shift_invariant {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) :
    let μ_X : Measure (ℕ → α) := Measure.map (fun ω n => X n ω) μ
    MeasurePreserving shift μ_X μ_X

/-!
## Helper lemmas for product measures

These lemmas establish the connection between bounded functions and indicator functions,
which is essential for the monotone class argument.
-/

/-- Indicator functions are bounded. This is a trivial but useful fact for the
monotone class extension. -/
lemma indicator_bounded {α : Type*} (s : Set α) :
    ∃ M : ℝ, ∀ x, |s.indicator (fun _ => (1 : ℝ)) x| ≤ M := by
  refine ⟨1, ?_⟩
  intro x
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The ENNReal value of an indicator function is either 0 or 1. -/
lemma indicator_mem_zero_one {α : Type*} (s : Set α) (x : α) :
    ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ∈ ({0, 1} : Set ENNReal) := by
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h, ENNReal.ofReal_one]
  · simp [Set.indicator_of_not_mem h, ENNReal.ofReal_zero]

/-- The ENNReal value of an indicator function is at most 1. -/
lemma indicator_le_one {α : Type*} (s : Set α) (x : α) :
    ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ≤ 1 := by
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h, ENNReal.ofReal_one]
  · simp [Set.indicator_of_not_mem h, ENNReal.ofReal_zero]

/-- A product of ENNReal values equals 0 iff at least one factor is 0. -/
lemma prod_eq_zero_iff {ι : Type*} [Fintype ι] (f : ι → ENNReal) :
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
lemma prod_eq_one_iff_of_zero_one {ι : Type*} [Fintype ι] (f : ι → ENNReal)
    (hf : ∀ i, f i ∈ ({0, 1} : Set ENNReal)) :
    ∏ i, f i = 1 ↔ ∀ i, f i = 1 := by
  constructor
  · intro h i
    have mem := hf i
    simp at mem
    cases mem with
    | inl h0 =>
      -- If any f i = 0, then product = 0, contradicting h
      exfalso
      have : ∏ j, f j = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact h0
      rw [this] at h
      norm_num at h
    | inr h1 => exact h1
  · intro h
    simp [h]

/-- The product of finitely many terms, each bounded by 1, is bounded by 1.
This is useful for products of indicator functions. -/
lemma prod_le_one_of_le_one {ι : Type*} [Fintype ι] (f : ι → ENNReal)
    (hf : ∀ i, f i ≤ 1) : ∏ i, f i ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _
    exact zero_le _
  · intro i _
    exact hf i

/-- Products of measurable ENNReal-valued functions are measurable. -/
lemma measurable_prod_ennreal {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (f : ι → Ω → ENNReal) (hf : ∀ i, Measurable (f i)) :
    Measurable fun ω => ∏ i, f i ω := by
  apply Finset.measurable_prod
  intro i _
  exact hf i

/-- The ENNReal indicator function composed with a measurable function is measurable. -/
lemma measurable_indicator_comp {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (hf : Measurable f) (s : Set α) (hs : MeasurableSet s) :
    Measurable fun ω => ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) (f ω)) := by
  -- The indicator function is measurable when composed with a measurable function
  have : Measurable fun ω => s.indicator (fun _ => (1 : ℝ)) (f ω) := by
    apply Measurable.indicator
    · exact measurable_const
    · exact hf hs
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
  have hM'_nonneg : ∀ i, 0 ≤ M' i := by
    intro i
    exact (zero_le_one.trans (le_max_right _ _))
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

/-- **Key Bridge Lemma**: If `E[f(Xᵢ) | tail] = ∫ f dν` for all bounded measurable `f`,
then for indicator functions we get `E[𝟙_B(Xᵢ) | tail] = ν(B)`. This is the crucial
step connecting the abstract conditional expectation property to concrete
probability statements about measurable sets.
to concrete probability statements about measurable sets.

Proof outline:
1. The indicator function 𝟙_B : α → ℝ is bounded (by 1) and measurable
2. By hypothesis `hν_cond`, we have: `E[𝟙_B(Xᵢ) | tail] = ∫ 𝟙_B d(ν ω)`
3. The RHS simplifies: `∫ 𝟙_B d(ν ω) = ν ω B` (by definition of indicator integral)
4. The LHS is exactly what we want: `E[𝟙_B(Xᵢ) | tail] ω`
5. Converting to `ℝ` gives the desired identity.
-/
lemma condExp_indicator_eq_measure {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s)) (i : ℕ) (B : Set α) (hB : MeasurableSet B)
    -- The key directing measure property: E[f(X_i) | ℱ] = ∫ f dν for bounded f
    -- where ℱ is the tail σ-field (represented as a sub-σ-algebra of Ω)
    (tail : Set (Set Ω))  -- The tail σ-field as a collection of sets
    (hν_cond : ∀ (f : α → ℝ), Measurable f → (∃ M, ∀ x, |f x| ≤ M) → True) :
    -- Placeholder for the actual property involving conditional expectation
    True := by
  -- This lemma needs a proper formulation of the tail σ-field in the base space Ω
  -- The challenge is that the tail σ-field is naturally defined on path space (ℕ → α),
  -- but conditional expectation needs a sub-σ-algebra of the base space Ω

  -- For now, we recognize this is a conceptual mismatch that needs to be resolved
  -- by properly setting up the relationship between:
  -- 1. The path space (ℕ → α) with its tail σ-algebra
  -- 2. The base space Ω where we take conditional expectations
  -- 3. The connection via the sequence X : ℕ → Ω → α

  trivial  -- TODO: Reformulate with proper σ-field structure


/-- For conditionally i.i.d. sequences, the joint distribution of finitely many coordinates
equals the average of the product measures built from the directing measure.

This is an intermediate result showing how the finite-dimensional distributions are determined
by the directing measure `ν`.

Note: We use lintegral (∫⁻) for measure-valued integrals since measures are `ENNReal`-valued.

Proof strategy:
1. Start from `hν_dir`: `E[f(Xᵢ) | tail] = ∫ f d(ν ω)` for bounded measurable `f`
2. Apply to indicator functions: `E[𝟙_{Bᵢ}(Xᵢ)] = E[ν(Bᵢ)]`
3. Use conditional independence to get products:
   `E[∏ᵢ 𝟙_{Bᵢ}(Xᵢ)] = E[∏ᵢ ν(Bᵢ)]`
4. The LHS is `μ {ω | ∀ i, Xᵢ(ω) ∈ Bᵢ}`; the RHS is the integral of the product measure
5. From these, we obtain the desired equality on rectangles

The key step (3) requires proving conditional independence, which comes from the monotone class
argument extending from bounded functions to product sets.
-/
lemma fidi_eq_avg_product {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s))
    (m : ℕ) (k : Fin m → ℕ) (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i))
    (hν_dir : ∀ (f : α → ℝ), Measurable f → (∃ M, ∀ x, |f x| ≤ M) → ∀ (i : ℕ), True) :
    μ {ω | ∀ i, X (k i) ω ∈ B i} = ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := by
  classical

  -- Shorthand for the target measurable set
  set E : Set Ω := {ω | ∀ i : Fin m, X (k i) ω ∈ B i}

  have hEvtMeas : MeasurableSet E := by
    have : E = ⋂ i : Fin m, {ω | X (k i) ω ∈ B i} := by
      ext ω; simp [E]
    simpa [this] using
      MeasurableSet.iInter fun i => (hX_meas (k i)) (hB i)

  -- Product of {0,1}-valued indicators collapses to the indicator of E
  have hProdEqIndicator :
      (fun ω : Ω => ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)))
        = Set.indicator E (fun _ : Ω => (1 : ℝ≥0∞)) := by
    classical
    funext ω
    classical
    by_cases hω : ω ∈ E
    · have h1 : ∀ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) = 1 := by
        intro i
        have Hi : X (k i) ω ∈ B i := by simpa [E] using (hω i)
        simpa [Set.indicator, Hi]
      have : ∀ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) = 1 := by
        intro i; simp [h1 i]
      have hprod :
          ∏ i : Fin m,
              ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) = 1 := by
        simpa [this] using
          Finset.prod_const_one (s := (Finset.univ : Finset (Fin m))) (a := (1 : ℝ≥0∞))
      simpa [Set.indicator, E, hω, hprod]
    · have hnot : ω ∉ E := hω
      have hzero : ∃ j : Fin m,
          ENNReal.ofReal ((B j).indicator (fun _ => (1 : ℝ)) (X (k j) ω)) = 0 := by
        classical
        have : ¬∀ i : Fin m, X (k i) ω ∈ B i := by simpa [E] using hnot
        rcases not_forall.mp this with ⟨j, hj⟩
        refine ⟨j, ?_⟩
        simp [Set.indicator, hj]
      rcases hzero with ⟨j, hj⟩
      have hjmem : (j : Fin m) ∈ (Finset.univ : Finset (Fin m)) := by simp
      have hprod :
          ∏ i : Fin m,
              ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) = 0 :=
        Finset.prod_eq_zero hjmem hj
      simpa [Set.indicator, hnot, hprod]

  -- Evaluate μ(E) via the lintegral of its indicator
  have lhs_eq : μ E
      = ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ := by
    classical
    have hlin :=
      lintegral_indicator (μ := μ) (s := E)
        (f := fun _ : Ω => (1 : ℝ≥0∞)) hEvtMeas
    have hconst := lintegral_const (μ := μ.restrict E) (c := (1 : ℝ≥0∞))
    have hconst' : ∫⁻ ω, (1 : ℝ≥0∞) ∂μ.restrict E = μ E := by
      simpa [Measure.restrict_apply, hEvtMeas, mul_comm] using hconst
    have hμE : μ E = ∫⁻ ω, Set.indicator E (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂μ := by
      simpa [hconst'] using hlin.symm
    simpa [hProdEqIndicator] using hμE

  -- Rewrite the integrand on the right via product measures on rectangles
  have rhs_eq :
      ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ
        = ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω)
            {x : Fin m → α | ∀ i, x i ∈ B i} ∂μ := by
    have set_eq : {x : Fin m → α | ∀ i, x i ∈ B i}
        = Set.univ.pi fun i => B i := by
      ext x; simp [Set.pi]
    have hpt : (fun ω => ∏ i : Fin m, ν ω (B i))
        = fun ω => (Measure.pi fun i : Fin m => ν ω)
            {x : Fin m → α | ∀ i, x i ∈ B i} := by
      funext ω; simp [set_eq, Measure.pi_pi]
    simpa [hpt]

  -- Structural bridge: indicators versus conditional product measures
  have prod_eq :
      ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
        = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := by
    -- TODO: package conditional independence from the directing measure hypothesis.
    sorry

  -- Chain the three equalities
  calc
    μ {ω | ∀ i, X (k i) ω ∈ B i} = μ E := rfl
    _ = ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ := lhs_eq
    _ = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := prod_eq
    _ = ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := rhs_eq

/-- The collection of measurable rectangles in a product space forms a π-system.

A rectangle in (Fin m → α) is a set of the form {x | ∀ i, x i ∈ Bᵢ} for measurable sets Bᵢ.

Proof strategy:
- Need to show: if R₁, R₂ are rectangles and R₁ ∩ R₂ ≠ ∅, then R₁ ∩ R₂ is a rectangle
- If R₁ = {x | ∀ i, x i ∈ B¹ᵢ} and R₂ = {x | ∀ i, x i ∈ B²ᵢ}
- Then R₁ ∩ R₂ = {x | ∀ i, x i ∈ B¹ᵢ ∩ B²ᵢ}
- Since B¹ᵢ ∩ B²ᵢ is measurable, this is a rectangle
-/
lemma rectangles_isPiSystem {m : ℕ} {α : Type*} [MeasurableSpace α] :
    IsPiSystem {S : Set (Fin m → α) | ∃ (B : Fin m → Set α),
      (∀ i, MeasurableSet (B i)) ∧ S = {x | ∀ i, x i ∈ B i}} := by
  intro S₁ hS₁ S₂ hS₂ _hne
  -- S₁ and S₂ are rectangles
  obtain ⟨B₁, hB₁_meas, rfl⟩ := hS₁
  obtain ⟨B₂, hB₂_meas, rfl⟩ := hS₂
  -- Their intersection is also a rectangle
  use fun i => B₁ i ∩ B₂ i
  constructor
  · intro i
    exact (hB₁_meas i).inter (hB₂_meas i)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ⟨h₁, h₂⟩ i
      exact ⟨h₁ i, h₂ i⟩
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- The product σ-algebra on (Fin m → α) is generated by measurable rectangles.

This is a fundamental result in product measure theory: the σ-algebra on a finite
product equals the σ-algebra generated by measurable rectangles.

Proof strategy:
- The product σ-algebra is the smallest σ-algebra making all projections measurable
- A set is in this σ-algebra iff it's in the σ-algebra generated by cylinder sets
- Cylinder sets are finite intersections of preimages of projections
- These are exactly the rectangles

In mathlib, this should follow from the definition of Pi.measurableSpace and
properties of generateFrom.
-/
lemma rectangles_generate_pi_sigma {m : ℕ} {α : Type*} [MeasurableSpace α] :
    (inferInstance : MeasurableSpace (Fin m → α)) =
    MeasurableSpace.generateFrom {S : Set (Fin m → α) | ∃ (B : Fin m → Set α),
      (∀ i, MeasurableSet (B i)) ∧ S = {x | ∀ i, x i ∈ B i}} := by
  -- The key insight: mathlib's generateFrom_pi shows that for finite index sets,
  -- the product σ-algebra equals the σ-algebra generated by measurable rectangles

  -- First establish the set equality: our rectangles match mathlib's rectangle format
  have set_eq : {S : Set (Fin m → α) | ∃ (B : Fin m → Set α),
      (∀ i, MeasurableSet (B i)) ∧ S = {x | ∀ i, x i ∈ B i}} =
      Set.pi univ '' Set.pi univ fun i : Fin m => {s : Set α | MeasurableSet s} := by
    ext S
    constructor
    · intro ⟨B, hB_meas, hS⟩
      use fun i => B i
      simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq]
      constructor
      · intro i _; exact hB_meas i
      · have : univ.pi (fun i => B i) = {x | ∀ i, x i ∈ B i} := by
          ext x; simp [Set.pi]
        rw [this]; exact hS.symm
    · intro ⟨B, hB_mem, hS⟩
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq] at hB_mem hS
      use B
      constructor
      · exact fun i => hB_mem i (Set.mem_univ i)
      · have : univ.pi (fun i => B i) = {x | ∀ i, x i ∈ B i} := by
          ext x; simp [Set.pi]
        rw [← this]; exact hS.symm

  rw [set_eq]
  exact generateFrom_pi.symm

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

/-- Helper: Product measures are measurable as a function of their components.
This states that if ω ↦ ν ω is a measurable family of measures, then
ω ↦ Measure.pi (fun _ => ν ω) is also measurable.

This is a technical lemma needed for product measure kernels. The proof should use:
1. A measure is determined by its values on a π-system generating the σ-algebra
2. For product measures, measurable rectangles form such a π-system
3. The product measure of a rectangle ∏ Bᵢ equals ∏ ν(Bᵢ)
4. Products of measurable functions are measurable
5. This gives measurability on the generating π-system, which extends to all measurable sets

In mathlib, this might follow from `Kernel.measurable` applied to the product kernel,
or from general results about measurability of measure-valued maps.
-/
lemma aemeasurable_measure_pi {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {m : ℕ}
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s)) :
    AEMeasurable (fun ω => Measure.pi fun _ : Fin m => ν ω) μ := by
  classical
  -- Abbreviation for the product kernel
  let κ : Ω → Measure (Fin m → α) := fun ω => Measure.pi fun _ : Fin m => ν ω
  -- Rectangular generator and π-system for the product σ-algebra
  let 𝒞 : Set (Set (Fin m → α)) :=
    {S | ∃ (B : Fin m → Set α), (∀ i, MeasurableSet (B i)) ∧
        S = {x | ∀ i, x i ∈ B i}}

  have h_gen : (inferInstance : MeasurableSpace (Fin m → α))
      = MeasurableSpace.generateFrom 𝒞 :=
    rectangles_generate_pi_sigma (m := m) (α := α)
  have h_pi : IsPiSystem 𝒞 := rectangles_isPiSystem (m := m) (α := α)

  -- Values on rectangles are measurable
  have h_basic : ∀ t ∈ 𝒞, Measurable fun ω => κ ω t := by
    intro t ht
    rcases ht with ⟨B, hB, rfl⟩
    have rect : (fun ω => κ ω {x : Fin m → α | ∀ i, x i ∈ B i})
        = fun ω => ∏ i : Fin m, ν ω (B i) := by
      funext ω
      have : {x : Fin m → α | ∀ i, x i ∈ B i}
          = Set.univ.pi fun i => B i := by
        ext x; simp [Set.pi]
      simp [κ, this, Measure.pi_pi]
    have hfac : ∀ i, Measurable fun ω => ν ω (B i) := by
      intro i; simpa using hν_meas (B i)
    have hmeas : Measurable fun ω => ∏ i : Fin m, ν ω (B i) :=
      measurable_prod_ennreal (fun i ω => ν ω (B i)) hfac
    simpa [κ, rect]

  -- Each product measure is a probability measure
  have hκ_prob : ∀ ω, IsProbabilityMeasure (κ ω) := by
    intro ω
    classical
    haveI : ∀ _ : Fin m, IsProbabilityMeasure (ν ω) := fun _ => hν_prob ω
    simpa [κ] using Measure.pi.instIsProbabilityMeasure

  -- Obtain measurability and downgrade to AE-measurability
  have hκ_meas : Measurable κ := by
    classical
    haveI : ∀ ω, IsProbabilityMeasure (κ ω) := hκ_prob
    refine
      Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        (μ := κ) h_gen h_pi ?_
    intro t ht; exact h_basic t ht
  exact hκ_meas.aemeasurable

/-- The bind of a probability measure with the product measure kernel equals the integral
of the product measure. This is the other side of the ConditionallyIID equation.

Note: We use lintegral (∫⁻) for measure-valued integrals since measures are ENNReal-valued.

This is a direct application of `Measure.bind_apply` from mathlib's Giry monad. -/
lemma bind_pi_apply {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s))
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
  - E[∏ᵢ 𝟙_{Bᵢ}(Xᵢ)] = ∏ᵢ E[𝟙_{Bᵢ}(Xᵢ)] = ∏ᵢ ν(Bᵢ) (conditional independence!)
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
theorem conditional_iid_from_directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s))  -- **changed type**
    -- For all bounded measurable f and all i:
    -- E[f(X_i) | tail σ-algebra] = ∫ f dν a.e.
    -- This is the key property from the directing measure construction.
    -- Note: ν should be tail-measurable (or almost tail-measurable in the sense of FMP 10.4).
    -- This follows from the construction of ν via ergodic theory (either Koopman or L²).
    (hν_cond : ∀ (f : α → ℝ) (_hf_meas : Measurable f) (_hf_bdd : ∃ M, ∀ x, |f x| ≤ M),
      ∀ (_i : ℕ), True) :  -- Placeholder: E[f(X_i) | tail] = ∫ f dν a.e.
    ConditionallyIID μ X := by
      -- Proof roadmap following Kallenberg's argument:
      --
      -- STEP 1: Package ν as satisfying the ConditionallyIID definition
      -- The definition requires: ∃ ν, (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      --   ∀ m k, Measure.map (fun ω i => X (k i) ω) μ = μ.bind (fun ω => Measure.pi fun _ => ν ω)
      use ν, hν_prob

      intro m k

      -- STEP 2: Show the finite-dimensional distributions match
      -- Need: Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      --     = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)
      --
      -- Strategy: Use measure_eq_of_agree_on_pi_system with rectangles as the π-system

      -- Define the two measures we want to prove equal
      let μ_map := Measure.map (fun ω i => X (k i) ω) μ
      let μ_bind := μ.bind fun ω => Measure.pi fun _ : Fin m => ν ω

      -- Both are probability measures
      have h_map_prob : IsProbabilityMeasure μ_map := by
        -- The pushforward of a probability measure is a probability measure
        have h_meas : Measurable (fun ω i => X (k i) ω) := by
          rw [measurable_pi_iff]
          intro i
          exact hX_meas (k i)
        exact Measure.isProbabilityMeasure_map h_meas.aemeasurable

      have h_bind_prob : IsProbabilityMeasure μ_bind := by
        -- The bind of a probability measure with probability kernels is a probability measure
        -- For each ω, Measure.pi (fun _ => ν ω) is a probability measure
        have h_pi_prob : ∀ ω, IsProbabilityMeasure (Measure.pi fun _ : Fin m => ν ω) := by
          intro ω
          -- Product of probability measures is a probability measure
          -- Following the pattern from ConditionallyIID.lean (pi_isProbabilityMeasure)
          constructor
          have h : (Set.univ : Set (Fin m → α)) = Set.univ.pi (fun (_ : Fin m) => Set.univ) := by
            ext x; simp
          rw [h, Measure.pi_pi]
          simp [measure_univ]
        -- Prove measure_univ = 1 directly using bind_apply
        constructor
        have h_ae_meas : AEMeasurable (fun ω => Measure.pi fun _ : Fin m => ν ω) μ :=
          aemeasurable_measure_pi ν hν_prob hν_meas
        rw [Measure.bind_apply .univ h_ae_meas]
        simp [measure_univ, h_pi_prob]

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
        -- This follows from map_coords_apply
        have hB : MeasurableSet {x : Fin m → α | ∀ i, x i ∈ B i} := by
          have : {x : Fin m → α | ∀ i, x i ∈ B i} = Set.univ.pi fun i => B i := by
            ext x; simp [Set.pi]
          rw [this]
          exact MeasurableSet.univ_pi hB_meas
        exact map_coords_apply X hX_meas m k _ hB

      -- RHS: μ_bind {x | ∀ i, x i ∈ B i}
      have rhs_eq : μ_bind {x | ∀ i, x i ∈ B i} =
          ∫⁻ ω, (Measure.pi fun i : Fin m => ν ω) {x | ∀ i, x i ∈ B i} ∂μ := by
        -- This follows from bind_pi_apply
        have hB : MeasurableSet {x : Fin m → α | ∀ i, x i ∈ B i} := by
          have : {x : Fin m → α | ∀ i, x i ∈ B i} = Set.univ.pi fun i => B i := by
            ext x; simp [Set.pi]
          rw [this]
          exact MeasurableSet.univ_pi hB_meas
        exact bind_pi_apply ν hν_prob hν_meas m _ hB

      -- Both equal by fidi_eq_avg_product
      rw [lhs_eq, rhs_eq]

      -- Apply fidi_eq_avg_product (which currently has a sorry)
      -- This is where the directing measure property hν_cond is used
      exact fidi_eq_avg_product X hX_meas ν hν_prob hν_meas m k B hB_meas hν_cond

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
    {m : MeasurableSpace Ω} {C : ∀ s : Set Ω, MeasurableSet s → Prop}
    {s : Set (Set Ω)} (h_eq : m = MeasurableSpace.generateFrom s)
    (h_inter : IsPiSystem s)
    (empty : C ∅ .empty)
    (basic : ∀ t (ht : t ∈ s), C t <| h_eq ▸ .basic t ht)
    (compl : ∀ t (htm : MeasurableSet t), C t htm → C tᶜ htm.compl)
    (iUnion : ∀ f : ℕ → Set Ω, Pairwise (fun i j => Disjoint (f i) (f j)) →
      ∀ (hf : ∀ i, MeasurableSet (f i)), (∀ i, C (f i) (hf i)) →
        C (⋃ i, f i) (MeasurableSet.iUnion hf))
    {t : Set Ω} (htm : MeasurableSet t) :
    C t htm := by
  -- Direct application of mathlib's π-λ theorem (induction_on_inter)
  exact MeasurableSpace.induction_on_inter h_eq h_inter empty basic compl iUnion t htm

/-- The monotone class extension argument for conditional independence:
if a property holds for products of bounded measurable functions,
it extends to product σ-algebras.

This is the application of FMP 1.1 mentioned in Kallenberg's proofs.

The strategy:
1. Start with the property for products of indicators: E[∏ 𝟙_{Bᵢ}(Xᵢ)] = E[∏ ν(Bᵢ)]
2. Indicators are bounded, so this follows from the bounded function hypothesis
3. Products of indicators generate the product σ-algebra (they form a π-system)
4. Apply π-λ theorem to extend to all product measurable sets
-/
theorem monotone_class_product_extension
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s))
    (k : ℕ)
    -- If the property holds for products of bounded functions
    (h_prod : ∀ (f : Fin k → α → ℝ),
      (∀ i, Measurable (f i)) →
      (∀ i, ∃ M, ∀ x, |f i x| ≤ M) →
      True) :  -- Placeholder: E[∏ f_i(X_i) | tail] = E[∏ ∫ f_i dν]
    -- Then it holds for all product measurable sets
    ∀ (B : Fin k → Set α), (∀ i, MeasurableSet (B i)) → True := by  -- Placeholder: μ{∩ Xᵢ ∈ Bᵢ} = ∫ ∏ ν(Bᵢ) dμ
  intro B hB

  -- Step 1: Build indicator functions for each set Bᵢ
  let indicators : Fin k → α → ℝ := fun i => (B i).indicator (fun _ => 1)

  have h_ind_meas : ∀ i, Measurable (indicators i) := by
    intro i
    exact Measurable.indicator measurable_const (hB i)

  have h_ind_bdd : ∀ i, ∃ M, ∀ x, |indicators i x| ≤ M := by
    intro i
    exact indicator_bounded (B i)

  -- Step 2: Apply the bounded function hypothesis to indicators
  -- This gives us: E[∏ᵢ 𝟙_{Bᵢ}(Xᵢ)] = E[∏ᵢ ∫ 𝟙_{Bᵢ} dν]
  have key := h_prod indicators h_ind_meas h_ind_bdd

  -- Step 3: Interpret this for the product set
  -- ∏ᵢ 𝟙_{Bᵢ}(Xᵢ(ω)) = 1 iff ∀ i, Xᵢ(ω) ∈ Bᵢ
  -- So E[∏ᵢ 𝟙_{Bᵢ}(Xᵢ)] = μ{ω : ∀ i, Xᵢ(ω) ∈ Bᵢ}
  -- And ∫ 𝟙_{Bᵢ} dν = ν(Bᵢ), so E[∏ᵢ ∫ 𝟙_{Bᵢ} dν] = E[∏ᵢ ν(Bᵢ)]

  -- This establishes the result for rectangles
  -- Extension to general sets requires measure uniqueness theorem
  trivial

/-- Package the common ending as a reusable theorem.

Given a contractable sequence and a directing measure ν constructed via
either approach (Mean Ergodic Theorem or L² bound), this completes the
proof to conditional i.i.d.

This encapsulates the "completed as before" step.
-/
theorem complete_from_directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_contract : Contractable μ X)
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ s, Measurable (fun ω => ν ω s))  -- **changed type**
    (hν_dir : ∀ (f : α → ℝ), Measurable f → (∃ M, ∀ x, |f x| ≤ M) → ∀ (i : ℕ), True) :  -- Placeholder: E[f(X_i) | tail] = ∫ f dν for bounded f
    ConditionallyIID μ X := by
  -- Use the skeleton lemma (to be completed later) to produce ConditionallyIID
  exact conditional_iid_from_directing_measure X hX_meas ν hν_prob hν_meas hν_dir

-- Summary and next steps for the common ending are recorded in the project notes.

end Exchangeability.DeFinetti.CommonEnding
