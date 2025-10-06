import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability

/-!
# Exchangeability (axiomatic stub)

To keep other parts of the project compiling while the full development is in
progress, we record the main results here as axioms together with proof
sketches. -/

noncomputable section

namespace Exchangeability

open MeasureTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Axiom**: measures on path space are determined by their finite-dimensional marginals.

Planned proof sketch (to be formalised here eventually):
- Set up `prefixProj n : (ℕ → α) → (Fin n → α)` and the cylinder family
  `prefixCylinders α := { (prefixProj n) ⁻¹' S | S measurable }`.
- Verify cylinders form a π-system by enlarging to
  `k = max m n` and restricting along `Fin.castLE`; measurability is inherited via
  `measurable_pi_apply`.
- Show `generateFrom prefixCylinders = ‹MeasurableSpace (ℕ → α)›` using the product
  σ-algebra characterisation (either
  `MeasurableSpace.pi_eq_generateFrom_projections` or
  `generateFrom_measurableCylinders`).
- With `IsFiniteMeasure μ` and `ν`, apply `Measure.ext_of_generate_finite` to the
  property `P A := μ A = ν A`; the hypothesis handles cylinders, while closure
  under complements and disjoint unions uses finiteness of μ, ν.
- No Ionescu–Tulcea machinery is required once this argument is written down. -/
axiom measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) μ S =
        Measure.map (fun f : ℕ → α => fun i : Fin n => f i) ν S) : μ = ν


/-- **Axiom**: exchangeability is equivalent to full exchangeability.

Implementation outline:
1. Form the path law `μ_X := map (ω ↦ fun i => X i ω) μ`. Finitary invariance
   from `Exchangeable μ X` says `map (reindex τ) μ_X = μ_X` for every permutation τ
   with finite support.
2. For a general permutation `π`, build `τₙ` agreeing with `π` on the first `n`
   coordinates. The construction can use `Equiv.Perm.extendSubtype` on the finite
   set `(range n) ∪ π '' (range n)`.
3. Push the equality for `τₙ` forward via each prefix projection to see that all
   finite-dimensional marginals of `μ_X` and `map (reindex π) μ_X` match.
4. Apply `measure_eq_of_fin_marginals_eq` to conclude
   `μ_X = map (reindex π) μ_X` and unravel the definition to obtain full
   exchangeability.
5. The reverse direction is immediate: specialise full invariance to finitary
   permutations and, if necessary, project onto the relevant coordinates. -/
axiom exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) : Exchangeable μ X ↔ FullyExchangeable μ X

end Exchangeability
