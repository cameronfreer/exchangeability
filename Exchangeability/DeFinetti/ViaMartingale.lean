/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp

/-!
# de Finetti's Theorem via Reverse Martingales

**Aldous' elegant martingale proof** of de Finetti's theorem, as presented in
Kallenberg (2005) as the "third proof". This approach has **medium dependencies**.

## Proof approach

The proof uses a contraction-independence lemma combined with reverse martingale
convergence:

1. **Lemma 1.3** (Contraction-Independence): If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`,
   then `ξ ⊥⊥_η ζ`.

   **Proof idea:** For any `B`, define `μ₁ = P[ξ ∈ B | η]` and `μ₂ = P[ξ ∈ B | ζ]`.
   Then `(μ₁, μ₂)` is a bounded martingale with `μ₁ =^d μ₂`, so
   `E(μ₂ - μ₁)² = Eμ₂² - Eμ₁² = 0`, implying `μ₁ = μ₂` a.s.

2. **Main theorem**: If `ξ` is contractable, then `ξₙ` are conditionally i.i.d.
  given the tail σ-algebra `𝒯_ξ = ⋂_n σ(θ_n ξ)`.

  From contractability: `(ξ_m, θ_{m+1} ξ) =^d (ξ_k, θ_{m+1} ξ)` for `k ≤ m`.
  Using Lemma 1.3 and reverse martingale convergence:
  ```
  P[ξ_m ∈ B | θ_{m+1} ξ] = P[ξ_k ∈ B | θ_{m+1} ξ] → P[ξ_k ∈ B | 𝒯_ξ]
  ```
   This shows conditional independence and identical conditional laws.

## Main results

* `deFinetti_viaMartingale`: **Main theorem** - contractable implies conditionally i.i.d.
* `contraction_independence`: Contraction-independence lemma (Kallenberg Lemma 1.3)

## Dependencies

⚖️ **Medium** - Requires martingale theory and reverse martingale convergence
✅ **Elegant** - Short and conceptually clear proof
✅ **Probabilistic** - Pure probability theory, no functional analysis

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Lemma 1.3 and page 28: "Third proof of Theorem 1.1"
* Aldous (1983), *Exchangeability and related topics*
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace ViaMartingale

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- `shiftProcess X m` is the process `n ↦ X (m + n)` (Kallenberg's θₘ ξ). -/
def shiftProcess (X : ℕ → Ω → α) (m : ℕ) : ℕ → Ω → α := fun n ω => X (m + n) ω

/-- The random path of a process: ω ↦ (n ↦ X n ω). -/
def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

/-- Shifted random path: ω ↦ (n ↦ X (m + n) ω). -/
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

section ComapTools

/-- If `g` is measurable, then `comap (g ∘ f) ≤ comap f`. -/
lemma comap_comp_le
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) :
    MeasurableSpace.comap (g ∘ f) (inferInstance : MeasurableSpace Z)
      ≤ MeasurableSpace.comap f (inferInstance : MeasurableSpace Y) := by
  intro s hs
  refine ⟨g ⁻¹' s, ?_, by ext x; rfl⟩
  exact hg hs

end ComapTools

section SequenceShift

variable {β : Type*} [MeasurableSpace β]

/-- Shift a sequence by dropping the first `d` entries. -/
def shiftSeq (d : ℕ) (f : ℕ → β) : ℕ → β := fun n => f (n + d)

@[simp]
lemma shiftSeq_apply {d : ℕ} (f : ℕ → β) (n : ℕ) :
    shiftSeq d f n = f (n + d) := rfl

lemma measurable_shiftSeq {d : ℕ} :
    Measurable (shiftSeq (β:=β) d) := by
  classical
  refine measurable_pi_iff.mpr ?_
  intro n
  -- Evaluation at `n + d` is measurable in the product σ-algebra.
  simp only [shiftSeq]
  exact measurable_pi_apply (n + d)

lemma forall_mem_erase {γ : Type*} [DecidableEq γ]
    {s : Finset γ} {a : γ} {P : γ → Prop} (ha : a ∈ s) :
    (∀ x ∈ s, P x) ↔ P a ∧ ∀ x ∈ s.erase a, P x := by
  constructor
  · intro h
    refine ⟨h _ ha, ?_⟩
    intro x hx
    exact h _ (Finset.mem_of_mem_erase hx)
  · rintro ⟨haP, hrest⟩ x hx
    by_cases hxa : x = a
    · simpa [hxa] using haP
    · have hx' : x ∈ s.erase a := by
        exact Finset.mem_erase.mpr ⟨hxa, hx⟩
      exact hrest _ hx'

end SequenceShift

section TailCylinders

variable {α}

/-- Cylinder on the first `r` tail coordinates (shifted by one). -/
def tailCylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f (i.1 + 1) ∈ C i}

variable [MeasurableSpace α]

/-- Basic measurability for tail cylinders. -/
lemma tailCylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (tailCylinder (α:=α) r C) := by
  classical
  refine MeasurableSet.iInter ?_
  intro i
  have hi : Measurable fun f : ℕ → α => f (i.1 + 1) :=
    measurable_pi_apply (i.1 + 1)
  simpa [tailCylinder] using hi (hC i)

end TailCylinders

section FinsetOrder

open Finset

lemma orderEmbOfFin_strictMono {s : Finset ℕ} :
    StrictMono fun i : Fin s.card => s.orderEmbOfFin rfl i := by
  classical
  simpa using (s.orderEmbOfFin rfl).strictMono

lemma orderEmbOfFin_mem {s : Finset ℕ} {i : Fin s.card} :
    s.orderEmbOfFin rfl i ∈ s := by
  classical
  simpa using Finset.orderEmbOfFin_mem (s:=s) (h:=rfl) i

lemma orderEmbOfFin_surj {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) :
    ∃ i : Fin s.card, s.orderEmbOfFin rfl i = x := by
  classical
  -- orderEmbOfFin is an order isomorphism, hence bijective onto s
  -- Use the fact that it's an injective function from a finite type to itself
  have h_inj : Function.Injective (s.orderEmbOfFin rfl : Fin s.card → ℕ) :=
    (s.orderEmbOfFin rfl).injective
  have h_range_sub : ∀ i, s.orderEmbOfFin rfl i ∈ s := orderEmbOfFin_mem (s:=s)
  -- Define a function to s viewed as a subtype
  let f : Fin s.card → s := fun i => ⟨s.orderEmbOfFin rfl i, h_range_sub i⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact h_inj (Subtype.ext_iff.mp hij)
  -- Injective function between finite types of equal cardinality is surjective
  have hf_surj : Function.Surjective f := Fintype.surjective_of_injective hf_inj
  obtain ⟨i, hi⟩ := hf_surj ⟨x, hx⟩
  use i
  exact Subtype.ext_iff.mp hi

/-- If `f : Fin n → ℕ` is strictly monotone and `a < f i` for all `i`,
then `Fin.cases a f : Fin (n+1) → ℕ` is strictly monotone. -/
lemma strictMono_fin_cases
    {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) {a : ℕ}
    (ha : ∀ i, a < f i) :
    StrictMono (Fin.cases a (fun i => f i)) := by
  intro i j hij
  classical
  cases' i using Fin.cases with _ i
  · cases' j using Fin.cases with _ j
    · exact False.elim ((lt_irrefl (0 : Fin (n + 1))) hij)
    · simpa using ha j
  · cases' j using Fin.cases with _ j
    ·
      have : ((Fin.succ i : Fin (n + 1)).1) < 0 := by
        simpa [Fin.lt_iff_val_lt_val] using hij
      exact False.elim ((Nat.not_lt.mpr (Nat.zero_le _)) this)
    ·
      have hij' : i < j := (Fin.succ_lt_succ_iff).1 hij
      simpa using hf hij'

end FinsetOrder

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma path_apply (X : ℕ → Ω → α) (ω n) :
    path X ω n = X n ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_apply (X : ℕ → Ω → α) (m ω n) :
    shiftRV X m ω n = X (m + n) ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_zero (X : ℕ → Ω → α) : shiftRV X 0 = path X := by
  funext ω n; simp [shiftRV, path]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_comp_shiftProcess (X : ℕ → Ω → α) (m k : ℕ) :
    shiftRV (shiftProcess X m) k = shiftRV X (m + k) := by
  funext ω n; simp [shiftRV, shiftProcess, Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftProcess_zero (X : ℕ → Ω → α) : shiftProcess X 0 = X := by
  funext n ω; simp [shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftProcess_add (X : ℕ → Ω → α) (m k : ℕ) :
    shiftProcess (shiftProcess X m) k = shiftProcess X (m + k) := by
  funext n ω; simp [shiftProcess, Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma path_eq_shiftRV_zero (X : ℕ → Ω → α) : path X = shiftRV X 0 :=
  (shiftRV_zero X).symm

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftProcess_apply (X : ℕ → Ω → α) (m n ω) :
    shiftProcess X m n ω = X (m + n) ω := by
  rfl

/-- 𝔽ₘ := σ(θₘ X) = σ(ω ↦ (n ↦ X (m+n) ω)). -/
abbrev revFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X m) inferInstance

@[simp]
lemma revFiltration_zero (X : ℕ → Ω → α) :
    revFiltration X 0 = MeasurableSpace.comap (path X) inferInstance := by
  simp [revFiltration]

/-- The tail σ-algebra for a process X: ⋂ₙ σ(Xₙ, Xₙ₊₁, ...). -/
def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, revFiltration X m

omit [MeasurableSpace Ω] in
@[simp]
lemma tailSigma_eq_iInf_rev (X : ℕ → Ω → α) :
    tailSigma X = ⨅ m, revFiltration X m := rfl

section Measurability

variable {X : ℕ → Ω → α}

lemma measurable_path (hX : ∀ n, Measurable (X n)) :
    Measurable (path X) := by
  classical
  simpa [path] using measurable_pi_iff.mpr hX

lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) {m : ℕ} :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

end Measurability

lemma revFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (revFiltration X) := by
  intro m k hmk
  have hcomp : shiftRV X k = (shiftSeq (β:=α) (k - m)) ∘ shiftRV X m := by
    funext ω n
    have hkm : m + (k - m) = k := by
      simpa using Nat.add_sub_of_le hmk
    have : m + (n + (k - m)) = k + n := by
      have : m + (n + (k - m)) = (m + (k - m)) + n := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [this, hkm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    simp [shiftRV, shiftSeq, Function.comp, this]
  have hmeas := measurable_shiftSeq (β:=α) (k - m)
  simpa [revFiltration, hcomp, Function.comp] using
    comap_comp_le (shiftRV X m) (shiftSeq (β:=α) (k - m)) hmeas

/-- If `X` is contractable, then so is each of its shifts `θₘ X`. -/
lemma shift_contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) : Contractable μ (shiftProcess X m) := by
  -- For any strictly monotone k : Fin n → ℕ, need to show:
  -- (shiftProcess X m (k i))ᵢ ~ (shiftProcess X m i)ᵢ
  intro n k hk_mono
  -- Define k' i = m + k i (strictly monotone)
  let k' : Fin n → ℕ := fun i => m + k i
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact Nat.add_lt_add_left (hk_mono hij) m
  -- Also define j i = m + i (for the RHS)
  let j : Fin n → ℕ := fun i => m + i
  have hj_mono : StrictMono j := by
    intro i₁ i₂ h
    simp only [j]
    exact Nat.add_lt_add_left h m
  -- Apply contractability to k' and j
  have h1 := hX n k' hk'_mono
  have h2 := hX n j hj_mono
  -- Now connect the pieces:
  -- (shiftProcess X m (k i))ᵢ = (X (m + k i))ᵢ = (X (k' i))ᵢ
  -- ~ (X i)ᵢ (by h1)
  -- ~ (X (j i))ᵢ (by h2.symm)
  -- = (X (m + i))ᵢ = (shiftProcess X m i)ᵢ
  calc Measure.map (fun ω i => shiftProcess X m (k i) ω) μ
      = Measure.map (fun ω i => X (k' i) ω) μ := by congr
    _ = Measure.map (fun ω i => X i.val ω) μ := h1
    _ = Measure.map (fun ω i => X (j i) ω) μ := h2.symm
    _ = Measure.map (fun ω i => shiftProcess X m i.val ω) μ := by congr

/-- **Lemma 1.3 (contraction and independence).**

If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.

**Proof sketch:** Fix a measurable set `B` and define:
- `μ₁ = P[ξ ∈ B | η]`
- `μ₂ = P[ξ ∈ B | ζ]`

Since `σ(η) ⊆ σ(ζ)`, we have that `μ₁` is `σ(η)`-measurable and `μ₂` is
`σ(ζ)`-measurable,
making `(μ₁, μ₂)` a bounded martingale. From the distributional equality
`(ξ, η) =^d (ξ, ζ)`, we get `μ₁ =^d μ₂`, so:

```
E(μ₂ - μ₁)² = E μ₂² - E μ₁² = 0
```

Thus `μ₁ = μ₂` a.s., i.e., `P[ξ ∈ B | η] = P[ξ ∈ B | ζ]` a.s. By Doob's
characterization of conditional independence (FMP 6.6), this gives `ξ ⊥⊥_η ζ`. ∎

*Kallenberg (2005), Lemma 1.3.* -/
lemma contraction_independence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ η ζ : Ω → α}
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
              = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_sigma : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance) :
    ProbabilityTheory.CondIndep ξ ζ η μ := by
  -- Proof path:
  -- 1. Use condexp_indicator_eq_of_dist_eq_and_le to get:
  --    E[1_{ξ∈B} | η] = E[1_{ξ∈B} | ζ] a.s. for all measurable B
  -- 2. By tower property and σ(η) ⊆ σ(ζ), this gives:
  --    E[1_{ξ∈B} | η ∨ ζ] = E[1_{ξ∈B} | η] a.s.
  -- 3. Apply Doob's characterization via condIndep_iff_condexp_eq
  --
  -- Note: CondIndep.of_indicator_condexp_eq provides this path for the
  -- specific case where ζ : Ω → ℕ → α (sequences). For general ζ : Ω → α,
  -- a similar lemma can be proven using the same approach.
  --
  -- TODO: Either generalize CondIndep.of_indicator_condexp_eq or prove directly
  -- via condIndep_iff product formula (same mathematical idea).
  sorry

/-- If `(ξ,η)` and `(ξ,ζ)` have the same law and `σ(η) ≤ σ(ζ)`,
then for all measurable `B`, the conditional expectations of `1_{ξ∈B}` coincide.

This is the key technical lemma that converts distributional equality into
conditional expectation equality. It's used to prove `condexp_convergence`. -/
lemma condexp_indicator_eq_of_dist_eq_and_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Ω → α} {η ζ : Ω → (ℕ → α)}
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
            = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (hσ : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap η inferInstance]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap ζ inferInstance] := by
  -- Proof sketch to implement in CondExp.lean:
  -- 1. Both sides are in [0,1] and in L² (indicators are bounded)
  -- 2. By hσ and tower property: E[(RHS - LHS) · g] = 0 for any g measurable w.r.t. σ(η)
  -- 3. Using h_dist, compare second moments:
  --    ∫ RHS² = ∫ LHS² (by distributional equality)
  --    Therefore ∫ (RHS - LHS)² = 0
  -- 4. Conclude RHS = LHS almost everywhere
  --
  -- Required lemmas from CondExp.lean:
  -- - condexp_tower: tower property for conditional expectation
  -- - condexp_L2_norm: ‖E[f|𝔾]‖₂ ≤ ‖f‖₂
  -- - indicator_L2: indicators are in L²
  -- - ae_eq_of_L2_norm_eq_zero: ‖f‖₂ = 0 ⇒ f = 0 a.e.
  sorry

/-- Finite-dimensional (cylinder) equality:
for any `r`, base set `B` and measurable sets on the first `r` tail coordinates,
the probabilities agree when comparing `(X m, θₘ X)` vs `(X k, θₘ X)`.

This is the exact finite-dimensional marginal needed for the martingale step. -/
lemma contractable_dist_eq_on_first_r_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (k m r : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
  classical
  -- reindex vectors of length r+1
  let κ_tail : Fin r → ℕ := fun i => m + (i.1 + 1)
  have h_tail : StrictMono κ_tail := by
    intro i j hij
    have hij' : i.1 < j.1 := by
      simpa [Fin.lt_iff_val_lt_val] using hij
    have : i.1 + 1 < j.1 + 1 := Nat.succ_lt_succ hij'
    simpa [κ_tail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_lt_add_left this m

  -- whole index vectors (head+tail)
  let κ₁ : Fin (r + 1) → ℕ := Fin.cases m (fun i : Fin r => κ_tail i)
  let κ₂ : Fin (r + 1) → ℕ := Fin.cases k (fun i : Fin r => κ_tail i)
  have hκ₁ : StrictMono κ₁ :=
    strictMono_fin_cases (f := κ_tail) h_tail (by
      intro i
      simpa [κ_tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.lt_add_of_pos_right (Nat.succ_pos (i.1)))
  have hκ₂ : StrictMono κ₂ :=
    strictMono_fin_cases (f := κ_tail) h_tail (by
      intro i
      have hm : m < m + (i.1 + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos (i.1))
      exact lt_of_le_of_lt hk
        (by
          simpa [κ_tail, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using hm))

  -- evaluation maps to the (r+1)-vector
  let φ₁ : Ω → (Fin (r + 1) → α) :=
    fun ω => Fin.cases (X m ω) (fun i : Fin r => X (κ_tail i) ω)
  let φ₂ : Ω → (Fin (r + 1) → α) :=
    fun ω => Fin.cases (X k ω) (fun i : Fin r => X (κ_tail i) ω)

  -- cylinder set in `(Fin (r+1) → α)`
  let A : Set (Fin (r + 1) → α) :=
    {y | y 0 ∈ B ∧ ∀ i : Fin r, y (Fin.succ i) ∈ C i}

  -- identify events as preimages of A
  have hE₁ :
      {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} = φ₁ ⁻¹' A := by
    ext ω; rfl
  have hE₂ :
      {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} = φ₂ ⁻¹' A := by
    ext ω; rfl

  -- contractability gives: both pushforwards = law of the canonical vector (X 0, X 1, …, X r)
  have hpush₁ :
      Measure.map φ₁ μ = Measure.map (fun ω (i : Fin (r + 1)) => X i.1 ω) μ := by
    simpa [φ₁] using hX (r + 1) κ₁ hκ₁
  have hpush₂ :
      Measure.map φ₂ μ = Measure.map (fun ω (i : Fin (r + 1)) => X i.1 ω) μ := by
    simpa [φ₂] using hX (r + 1) κ₂ hκ₂

  -- measurable A (so we can evaluate measures)
  have hA : MeasurableSet A := by
    classical
    have h0 : Measurable (fun y : (Fin (r + 1) → α) => y 0) := measurable_pi_apply 0
    have hS : ∀ i, Measurable (fun y : (Fin (r + 1) → α) => y (Fin.succ i)) :=
      fun i => measurable_pi_apply (Fin.succ i)
    refine (h0 hB).and ?_
    refine MeasurableSet.iInter ?_
    intro i
    simpa using (hS i (hC i))

  -- take measures of A under both pushforwards
  have : (Measure.map φ₁ μ) A = (Measure.map φ₂ μ) A := by
    -- both equal the canonical pushforward's measure of A
    simpa [hpush₁] using congrArg (fun ν => ν A) hpush₂.symm

  -- unfold and conclude
  simpa [hE₁, hE₂, Measure.map_apply, hA] using this

/-- Helper lemma: contractability gives the key distributional equality.

If `X` is contractable, then for any `k ≤ m`:
```
(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)
```
where `θ_{m+1} X` drops the first coordinate and keeps the *future* tail
`ω ↦ (n ↦ X(m + 1 + n) ω)`. -/
lemma contractable_dist_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m) :
    Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ
      = Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ := by
  classical
  have hrect :=
    agree_on_future_rectangles_of_contractable
      (μ:=μ) (X:=X) hX k m hk
  simpa using AgreeOnFutureRectangles_to_measure_eq hrect

/-- **Key convergence result:** The extreme members agree after conditioning on the tail σ-algebra.

For any `k ≤ m` and measurable set `B`:
```
P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X] → P[X_k ∈ B | 𝒯_X]  (as n → ∞)
```

This is proved using Lemma 1.3 (contraction-independence) followed by reverse
martingale convergence. -/
-- TODO: The following theorems require conditional expectation API that is not yet
-- fully developed in this codebase. The proof structure is documented for future work.

lemma condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | futureFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | futureFiltration X m] := by
  classical
  have hshift := measurable_shiftRV (hX := hX_meas) (m := m + 1)
  have hagree := agree_on_future_rectangles_of_contractable
    (μ := μ) (X := X) hX k m hk
  have hlemma :=
    Exchangeability.Probability.condexp_indicator_eq_of_agree_on_future_rectangles
      (μ := μ) (X₁ := fun ω => X m ω) (X₂ := fun ω => X k ω)
      (Y := shiftRV X (m + 1))
      (hX₁ := hX_meas m) (hX₂ := hX_meas k) (hY := hshift)
      (hagree := hagree) B hB
  simpa [futureFiltration]
    using hlemma

lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  classical
  -- Notation
  set f_m : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ)) ∘ X m)
  set f_0 : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ)) ∘ X 0)

  -- (1) Levelwise equality at σ(θ_{m+1}X) from your rectangles lemma
  have h_level :
      μ[f_m | futureFiltration X m] =ᵐ[μ] μ[f_0 | futureFiltration X m] := by
    -- This is exactly your `condexp_convergence` specialized to k=0
    have hk : 0 ≤ m := Nat.zero_le m
    exact
      (condexp_convergence (μ:=μ) (X:=X) hX hX_meas (k:=0) (m:=m) hk B hB)

  -- (2) Tail σ-algebra is below every futureFiltration
  have hTail_le_future :
      tailSigma X ≤ futureFiltration X m := by
    -- tail = ⨅ n futureFiltration X n, so ≤ any one of them
    have : tailSigmaFuture X = ⨅ n, futureFiltration X n := rfl
    have h' : tailSigma X = tailSigmaFuture X := (tailSigmaFuture_eq_tailSigma X).symm
    simpa [h', this] using iInf_le (fun n => futureFiltration X n) m

  -- (3) Measurability fact used by setIntegral_condExp
  set Y := shiftRV X (m + 1)
  have hY : Measurable Y := measurable_shiftRV (hX := hX_meas) (m := m + 1)
  have hmY : futureFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := by
    -- comap Y ≤ ⊥-extension; unfold and use measurability of Y
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact hY ht

  -- (4) Equality of set integrals over every A in the tail σ-algebra
  have h_setInt_eq :
      ∀ {A : Set Ω}, MeasurableSet[tailSigma X] A →
        ∫ ω in A, f_m ω ∂μ = ∫ ω in A, f_0 ω ∂μ := by
    intro A hA
    -- A is measurable at every future level; in particular at m
    have hA_m : MeasurableSet[futureFiltration X m] A :=
      hTail_le_future _ hA
    -- Evaluate ∫_A f_m using condExp at level m
    have hint_m : Integrable f_m μ :=
      (integrable_const (1 : ℝ)).indicator ((hX_meas m) hB)
    have hint_0 : Integrable f_0 μ :=
      (integrable_const (1 : ℝ)).indicator ((hX_meas 0) hB)
    have hCE_m :=
      setIntegral_condExp (μ := μ) (m := futureFiltration X m) (hm := hmY)
        (f := f_m) hint_m hA_m
    have hCE_0 :=
      setIntegral_condExp (μ := μ) (m := futureFiltration X m) (hm := hmY)
        (f := f_0) hint_0 hA_m
    -- Replace CE(f_m|⋯) by CE(f_0|⋯) on A using the a.e. equality h_level
    have h_swap :
        ∫ ω in A, μ[f_m | futureFiltration X m] ω ∂μ
          = ∫ ω in A, μ[f_0 | futureFiltration X m] ω ∂μ := by
      refine setIntegral_congr_ae ?_ (ae_restrict_of_ae h_level)
      exact hA_m
    -- Chain equalities:
    -- ∫_A f_m = ∫_A CE_m(f_m) = ∫_A CE_m(f_0) = ∫_A f_0
    calc
      ∫ ω in A, f_m ω ∂μ
          = ∫ ω in A, μ[f_m | futureFiltration X m] ω ∂μ := hCE_m.symm
      _ = ∫ ω in A, μ[f_0 | futureFiltration X m] ω ∂μ := h_swap
      _ = ∫ ω in A, f_0 ω ∂μ := hCE_0

  -- (5) Use uniqueness of CE on the tail: CE_tail(f_m) = CE_tail(f_0)
  have hmTail :
      tailSigma X ≤ (inferInstance : MeasurableSpace Ω) := by
    intro s hs; exact hs  -- every tail-measurable set is measurable in Ω
  -- we choose g := CE_tail(f_0)
  have g_meas :
      StronglyMeasurable[tailSigma X] (μ[f_0 | tailSigma X]) :=
    stronglyMeasurable_condexp
  have g_int : Integrable (μ[f_0 | tailSigma X]) μ := integrable_condexp
  have h_target :
      μ[f_m | tailSigma X] =ᵐ[μ] μ[f_0 | tailSigma X] := by
    -- apply uniqueness with the set-integral identity proved above
    refine
      (ae_eq_condExp_of_forall_setIntegral_eq
        (μ := μ) (m := tailSigma X) (hm := hmTail)
        (f := f_m) (g := μ[f_0 | tailSigma X])
        (hf_int := (integrable_const (1 : ℝ)).indicator ((hX_meas m) hB))
        (hg_int := g_int)
        (h_set_integral_eq := ?_)
        (hg_meas := g_meas)).symm
    intro A hA
    -- ∫_A f_m = ∫_A f_0, and ∫_A CE_tail(f_0) = ∫_A f_0
    have := h_setInt_eq hA
    simpa [setIntegral_condExp (μ := μ) (m := tailSigma X) (hm := hmTail)
            (f := f_0) ((integrable_const (1 : ℝ)).indicator ((hX_meas 0) hB)) hA]
      using this

  simpa [f_m, f_0] using h_target

/--
Additive “future-filtration + standard-cylinder” layer that coexists with the
current `revFiltration` / `tailCylinder` infrastructure. Existing names remain intact.
-/

/-! ## Future filtration (additive) -/
section FutureFiltration

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Future reverse filtration: 𝔽ᶠᵘᵗₘ = σ(θ_{m+1} X). -/
abbrev futureFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance

/-- The future filtration is decreasing (antitone). -/
lemma futureFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (futureFiltration X) := by
  intro m n hmn
  simpa [futureFiltration, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (revFiltration_antitone X (Nat.succ_le_succ hmn))

/-- Tail σ-algebra via the future filtration. (Additive alias.) -/
def tailSigmaFuture (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, futureFiltration X m

@[simp] lemma tailSigmaFuture_eq_iInf (X : ℕ → Ω → α) :
    tailSigmaFuture X = ⨅ m, futureFiltration X m := rfl

@[simp] lemma futureFiltration_eq_rev_succ (X : ℕ → Ω → α) (m : ℕ) :
    futureFiltration X m = revFiltration X (m + 1) := rfl

lemma tailSigmaFuture_eq_tailSigma (X : ℕ → Ω → α) :
    tailSigmaFuture X = tailSigma X := by
  classical
  have hfut : tailSigmaFuture X = ⨅ n, revFiltration X (n + 1) := by
    simpa [tailSigmaFuture, futureFiltration_eq_rev_succ]
  have htail : tailSigma X = ⨅ n, revFiltration X n := rfl
  refine le_antisymm ?_ ?_
  · -- `tailSigmaFuture ≤ tailSigma`
    refine (hfut ▸ ?_)
    refine le_iInf ?_
    intro n
    have h1 : (⨅ m, revFiltration X (m + 1)) ≤ revFiltration X (n + 1) :=
      iInf_le (fun m => revFiltration X (m + 1)) n
    have h2 : revFiltration X (n + 1) ≤ revFiltration X n := by
      simpa [Nat.succ_eq_add_one]
        using revFiltration_antitone X (Nat.succ_le_succ (Nat.le_refl n))
    exact h1.trans h2
  · -- `tailSigma ≤ tailSigmaFuture`
    refine (htail ▸ ?_)
    refine le_iInf ?_
    intro n
    have h1 : (⨅ m, revFiltration X m) ≤ revFiltration X (n + 1) :=
      iInf_le (fun m => revFiltration X m) (n + 1)
    simpa [futureFiltration_eq_rev_succ] using h1

end FutureFiltration

/-! ## Standard cylinders on paths (starting at index 0) -/
section FutureCylinders

variable {α : Type*}

/-- Standard cylinder on the first `r` coordinates starting at index 0. -/
def cylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

variable [MeasurableSpace α]

lemma cylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (cylinder (α:=α) r C) := by
  classical
  refine MeasurableSet.iInter ?_
  intro i
  have hi : Measurable fun f : (ℕ → α) => f i := measurable_pi_apply i
  simpa [cylinder] using hi (hC i)

end FutureCylinders

/-! ## Product of indicators for finite cylinders -/

/-- Product of indicator functions for a finite cylinder on the first `r` coordinates. -/
def indProd {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Ω → ℝ :=
  fun ω => ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)

lemma indProd_as_indicator
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C
      = Set.indicator {ω | ∀ i : Fin r, X i ω ∈ C i} (fun _ => (1 : ℝ)) := by
  classical
  funext ω
  -- Each factor is 0/1; the product is 1 iff all factors are 1.
  induction r with
  | zero => simp [indProd]  -- r = 0 : empty product = 1; the set is `univ`.
  | succ r ih =>
    -- Move from r to r+1
    have : indProd X (r + 1) C ω
        = indProd X r (fun j => C (Fin.castSucc j)) ω
          * Set.indicator (C ⟨r, Nat.lt_succ_self r⟩) (fun _ => (1 : ℝ)) (X r ω) := by
      simp [indProd, Fin.prod_univ_succ]
    simp [this, ih, Set.indicator, Fin.forall_fin_succ]

/-- Basic integrability: `indProd` is an indicator of a measurable set, hence integrable. -/
lemma indProd_integrable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} (X : ℕ → Ω → α)
    (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Integrable (indProd X r C) μ := by
  classical
  have hSet :
      MeasurableSet {ω | ∀ i : Fin r, X i ω ∈ C i} := by
    refine MeasurableSet.iInter ?_
    intro i
    have : Measurable fun ω => X i ω := hX i
    simpa using this (hC i)
  simpa [indProd_as_indicator X r C]
    using (integrable_const (1 : ℝ)).indicator hSet

/-- Drop the first coordinate of a path. -/
def drop {α : Type*} (f : ℕ → α) : ℕ → α := shiftSeq (β:=α) 1 f

@[simp] lemma drop_apply {α : Type*} (f : ℕ → α) (n : ℕ) :
    drop f n = f (n + 1) := rfl

section CylinderBridge

variable {α : Type*} [MeasurableSpace α]

lemma measurable_drop : Measurable (drop : (ℕ → α) → (ℕ → α)) := by
  simpa [drop] using (measurable_shiftSeq (β:=α) (d:=1))

/-- `tailCylinder` is the preimage of a standard cylinder under `drop`. -/
lemma tailCylinder_eq_preimage_cylinder
    {r : ℕ} {C : Fin r → Set α} :
    tailCylinder (α:=α) r C
      = (drop : (ℕ → α) → (ℕ → α)) ⁻¹' (cylinder (α:=α) r C) := by
  ext f
  constructor <;> intro hf
  · simpa [tailCylinder, drop, shiftSeq, cylinder]
  · simpa [tailCylinder, drop, shiftSeq, cylinder]

@[simp] lemma mem_cylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
    f ∈ cylinder (α:=α) r C ↔ ∀ i : Fin r, f i ∈ C i := Iff.rfl

@[simp] lemma mem_tailCylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
    f ∈ tailCylinder (α:=α) r C ↔ ∀ i : Fin r, f (i.1 + 1) ∈ C i := Iff.rfl

end CylinderBridge

/-! ## Rectangles using future tails and standard cylinders -/
section FutureRectangles

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

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
      have : (shiftRV X (m + 1) ω) ∈ cylinder (α:=α) r C := hC
      simpa [ψ, cylinder, shiftRV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using this i
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      have : X (m + 1 + i.1) ω ∈ C i := hC i
      simpa [ψ, cylinder, shiftRV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using this

/-- **Finite-dimensional equality on future rectangles with standard cylinders.**
For `k ≤ m` and measurable `B`, the measures of
`B × cylinder r C` under the pushforwards by
`ω ↦ (X m ω, θ_{m+1}X(ω))` and `ω ↦ (X k ω, θ_{m+1}X(ω))` coincide. -/
lemma contractable_dist_eq_on_rectangles_future
    {X : ℕ → Ω → α} (hX : Contractable μ X)
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
    simpa [ψ₁, preimage_rect_future (μ:=μ) (X:=X) m m r B C]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simpa [ψ₂, preimage_rect_future (μ:=μ) (X:=X) k m r B C]
  have hfd :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      =
    μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (contractable_dist_eq_on_first_r_tail
        (μ:=μ) (X:=X) hX k m r hk B hB C hC)
  have : μ (ψ₁ ⁻¹' (B ×ˢ cylinder (α:=α) r C))
        = μ (ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)) := by
    simpa [hpre₁, hpre₂]
  simpa [Measure.map_apply, hrect, ψ₁, ψ₂] using this

end FutureRectangles

/-- Use the AgreeOnFutureRectangles from CondExp (which just wraps measure equality). -/
abbrev AgreeOnFutureRectangles := Exchangeability.Probability.AgreeOnFutureRectangles

lemma agree_on_future_rectangles_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m) :
    AgreeOnFutureRectangles
      (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
      (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ) := by
  classical
  refine ⟨?_⟩
  -- Direct measure equality from contractable_dist_eq
  exact contractable_dist_eq (μ:=μ) (X:=X) hX k m hk

/-! ## Measure extension from future rectangles -/

lemma measure_ext_of_future_rectangles
    {μ ν : Measure (α × (ℕ → α))}
    (h : ∀ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
        (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
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
    -- Intersection of rectangles is a rectangle of higher dimension
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
        · simpa [C, h1, h2] using (MeasurableSet.univ : MeasurableSet (Set.univ))

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
        have hi : (i : ℕ) < r := i.2
        have := hC' ⟨i, hi⟩
        classical
        have h1 : (i : ℕ) < r₁ := lt_of_lt_of_le i.2 (Nat.le_max_left _ _)
        by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2] at this
          exact this.1
        · simp [C, h1, h2] at this
      · intro i
        have hi : (i : ℕ) < r := i.2
        have := hC' ⟨i, hi⟩
        classical
        have h2 : (i : ℕ) < r₂ := lt_of_lt_of_le i.2 (Nat.le_max_right _ _)
        by_cases h1 : (i : ℕ) < r₁
        · simp [C, h1, h2] at this
          exact this.2
        · simp [C, h1, h2] at this

  -- Show that S generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace (α × (ℕ → α)))
      = MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      rcases hs with ⟨r, B, hB, C, hC, rfl⟩
      exact hB.prod (cylinder_measurable (α:=α) hC)
    · -- Using the characterization of the product σ-algebra
      have : (inferInstance : MeasurableSpace (α × (ℕ → α)))
          = MeasurableSpace.comap Prod.fst inferInstance ⊔
            MeasurableSpace.comap Prod.snd inferInstance :=
        by simpa using (MeasurableSpace.prod_eq : _)
      refine this ▸ sup_le ?_ ?_
      · -- First component
        refine (MeasurableSpace.comap_le_iff_le_map).1 ?_
        apply MeasurableSpace.generateFrom_le
        intro B hB
        have : Prod.fst ⁻¹' B = B ×ˢ Set.univ := by
          ext ⟨a, f⟩; simp
        refine this ▸ ?_
        have : B ×ˢ Set.univ =
            B ×ˢ cylinder (α:=α) 0 (fun _ => Set.univ) := by
          ext ⟨a, f⟩; simp [cylinder]
        refine MeasurableSpace.measurableSet_generateFrom ?_
        exact ⟨0, B, hB, _, fun _ => MeasurableSet.univ, this.symm⟩
      · -- Second component
        refine (MeasurableSpace.comap_le_iff_le_map).1 ?_
        apply MeasurableSpace.generateFrom_le
        intro T hT
        rcases hT with ⟨i, D, hD, rfl⟩
        have : Prod.snd ⁻¹' {f | f i ∈ D}
            = Set.univ ×ˢ {f : ℕ → α | f i ∈ D} := by
          ext ⟨a, f⟩; simp
        refine this ▸ ?_
        -- Encode `{f | f i ∈ D}` as a cylinder
        let C : Fin (i + 1) → Set α := fun j =>
          if h : (j : ℕ) = i then D else Set.univ
        have hC : ∀ j, MeasurableSet (C j) := by
          intro j
          classical
          by_cases h : (j : ℕ) = i
          · simpa [C, h] using hD
          · simpa [C, h] using (MeasurableSet.univ : MeasurableSet (Set.univ))
        have h_cyl :
            {f : ℕ → α | f i ∈ D} = cylinder (α:=α) (i + 1) C := by
          ext f; constructor
          · intro hfi
            intro j
            classical
            by_cases h : (j : ℕ) = i
            · subst h; simpa [C] using hfi
            · simp [C, h]
          · intro hf
            have := hf ⟨i, Nat.lt_succ_self i⟩
            simpa [C, show ((⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)) : ℕ) = i by rfl]
              using this
        have : Set.univ ×ˢ {f : ℕ → α | f i ∈ D}
            = Set.univ ×ˢ cylinder (α:=α) (i + 1) C := by
          simp [h_cyl]
        refine MeasurableSpace.measurableSet_generateFrom ?_
        exact ⟨i + 1, Set.univ, MeasurableSet.univ, C, hC, this.symm⟩

  -- Measures agree on S
  have h_agree : ∀ s ∈ S, μ s = ν s := by
    intro s hs
    rcases hs with ⟨r, B, hB, C, hC, rfl⟩
    exact h r B hB C hC

  -- Covering family
  let Bseq : ℕ → Set (α × (ℕ → α)) := fun _ => Set.univ
  have h1B : ⋃ n, Bseq n = Set.univ := by simp [Bseq]
  have h2B : ∀ n, Bseq n ∈ S := by
    intro n
    refine ⟨0, Set.univ, MeasurableSet.univ,
      (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
    ext ⟨a, f⟩; simp [Bseq, cylinder]
  have hμB : ∀ n, μ (Bseq n) ≠ ∞ := by
    intro n; simp [Bseq]

  exact Measure.ext_of_generateFrom_of_iUnion
    S Bseq h_gen h_pi h1B h2B hμB h_agree

/-- The measure_eq field is now directly accessible since we simplified the structure. -/
lemma AgreeOnFutureRectangles_to_measure_eq
    {μ ν : Measure (α × (ℕ → α))}
    (h : AgreeOnFutureRectangles μ ν) : μ = ν :=
  h.measure_eq


section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ := σ(θ_{m+1} X) (the future filtration). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := futureFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone : Antitone 𝔽 := by
  intro m n hmn
  simpa [𝔽] using futureFiltration_antitone X hmn

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B. -/
def M (k : ℕ) (B : Set α) : ℕ → Ω → ℝ :=
  fun m ω =>
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | 𝔽 m] ω

-- TODO (CondExp.lean milestones):
-- (1) `0 ≤ M k B m ω ≤ 1` a.s.
--     API: `condexp_indicator_bounds`.
-- (2) For `m ≤ n`, `M k B n` is `𝔽 n`-measurable and
--     `μ[fun ω => M k B n ω | 𝔽 m] =ᵐ[μ] M k B m`.
--     API: `condexp_tower`, `condexp_stronglyMeasurable`.
-- (3) If `(X m, θₘ X) =^d (X k, θₘ X)`, then
--     `M m B m =ᵐ[μ] M k B m`.
--     API: `condexp_indicator_eq_of_dist_eq_and_le`.
-- (4) `(fun n => M k B n ω)` is a reverse martingale that converges
--     to `μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | tailSigma X] ω`.
--     API: `condexp_tendsto_condexp_iInf` (Lévy's downward theorem) together with
--     `filtration_antitone` and `tailSigmaFuture_eq_iInf`.

end reverse_martingale

/-! ## Tail factorization on finite cylinders -/

/-! ### Helper lemmas for finite-level factorization -/

/-- For contractable sequences, X_i and the future shift are conditionally independent
given any later future filtration. This is a key consequence of contractability. -/
axiom coordinate_future_condIndep
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (i m : ℕ) (hm : m > i) :
    ProbabilityTheory.CondIndep
      (futureFiltration X m)
      (MeasurableSpace.comap (X i) inferInstance)
      (MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance)
      (futureFiltration_le X m)
      μ

/-- Conditional expectation of products factors when coordinates are conditionally
independent. This is a wrapper around the general product rule for conditional expectations. -/
axiom condExp_product_of_condIndep
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    (hm : m ≤ inferInstance)
    (f g : Ω → ℝ)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hf_meas : AEStronglyMeasurable[m] f μ)
    (hg_meas : StronglyMeasurable g)
    (h_indep : ∀ A B, MeasurableSet[m] A → MeasurableSet B →
        μ[A.indicator (fun _ => (1 : ℝ)) | m] * μ[B.indicator (fun _ => (1 : ℝ)) | m]
          =ᵐ[μ] μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]) :
    μ[(fun ω => f ω * g ω) | m] =ᵐ[μ] (fun ω => μ[f | m] ω * g ω)

/-- **Finite-level factorization builder.**

For a contractable sequence, at any future level `m ≥ r`, the conditional expectation
of the product indicator factors:
```
μ[∏ᵢ<r 1_{Xᵢ∈Cᵢ} | σ(θₘ₊₁X)] = ∏ᵢ<r μ[1_{X₀∈Cᵢ} | σ(θₘ₊₁X)]
```

This iteratively applies `condIndep_of_indicator_condexp_eq` to pull out one coordinate
at a time, using contractability to replace each `Xᵢ` with `X₀`. -/
lemma finite_level_factorization
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    (m : ℕ) (hm : m ≥ r) :
    μ[indProd X r C | futureFiltration X m]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
        μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
  -- Proof by induction on r, factoring out one coordinate at a time
  induction r with
  | zero =>
    -- Base case: empty product = 1 on both sides
    simp [indProd, Finset.prod_empty]
    -- Both sides are the constant function 1, so they're equal a.e.
    have : (fun ω => (1 : ℝ)) =ᵐ[μ] μ[(fun _ => (1 : ℝ)) | futureFiltration X m] := by
      exact (condExp_const (hm := futureFiltration_le X m) (1 : ℝ)).symm
    exact this
  | succ r ih =>
    -- Inductive step: factor out the last coordinate X_r
    -- Strategy:
    -- 1. Split indProd into product of first r coordinates and last coordinate
    -- 2. Use contractability: X_r has same conditional law as X_0 given future
    -- 3. Use conditional independence to factor the product
    -- 4. Apply inductive hypothesis to the first r coordinates

    -- For now, this requires several technical lemmas about:
    -- - How indProd splits under Fin.succ
    -- - Conditional independence from contractability
    -- - Factoring conditional expectations of products
    sorry

/-- **Tail factorization on finite cylinders.**

Assume you have, for all large enough `m`, the finite‑level factorization
at the future filtration:
```
μ[indProd X r C | σ(θ_{m+1}X)]
  = ∏ i<r μ[1_{X₀∈C i} | σ(θ_{m+1}X)]   a.s.
```
Then the same factorization holds **at the tail σ‑algebra**:
```
μ[indProd X r C | 𝒯_X]
  = ∏ i<r μ[1_{X₀∈C i} | 𝒯_X]           a.s.
```

This passes the finite‑level equality to the tail using bounded
dominated convergence together with reverse martingale convergence. -/
axiom tail_factorization_from_future
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    -- finite-level factorization hypothesis (available after applying the wrapper repeatedly)
    (h_fact :
      ∀ m ≥ r,  -- any `m` with at least r future steps works
        μ[indProd X r C | futureFiltration X m]
          =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω))
    -- reverse-martingale convergence for each singleton factor
    (h_rev :
      ∀ i : Fin r,
        (∀ᵐ ω ∂μ,
          Tendsto (fun m => μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0)
                                 | futureFiltration X m] ω)
                  atTop
                  (𝓝 (μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0)
                          | tailSigma X] ω)))) :
    μ[indProd X r C | tailSigma X]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
        μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω)

/-- **Key lemma: All coordinates have identical conditional distributions.**

For a contractable sequence, all coordinates X_m have the same conditional law given
the tail σ-algebra. This follows immediately from `extreme_members_equal_on_tail`. -/
lemma identical_conditional_laws
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) :
    ∀ B : Set α, MeasurableSet B →
      μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
        =ᵐ[μ]
      μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] :=
  fun B hB => extreme_members_equal_on_tail hX hX_meas m B hB

/-- **Aldous' third proof of de Finetti's theorem.**

If `X` is contractable, then `X₁, X₂, ...` are conditionally i.i.d. given the
tail σ-algebra `𝒯_X = ⋂_n σ(θ_n X)`.

**Proof structure:**
1. From contractability: `(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)` for `k ≤ m ≤ n`
2. Define `𝒯_X = ⋂_n σ(θ_n X)` (tail σ-algebra)
3. Apply Lemma 1.3 + reverse martingale convergence:
   ```
   P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X] → P[X_k ∈ B | 𝒯_X]
   ```
4. Conclude: `P[X_m ∈ B | θ_{m+1} X] = P[X_m ∈ B | 𝒯_X] = P[X_1 ∈ B | 𝒯_X]`
5. First equality: `X_m ⊥⊥_{𝒯_X} θ_{m+1} X` for all `m`
6. By iteration: `X₁, X₂, ...` conditionally independent given `𝒯_X`
7. Second equality: conditional laws agree, giving conditional i.i.d.

*Kallenberg (2005), third proof of Theorem 1.1 (page 28).* -/
/-! ### Step 1: Constructing the directing measure ν

From conditional expectations on indicators, we need to build a measurable family
of probability measures `ν : Ω → Measure α`.

The construction uses the standard Borel machinery: for each `ω`, define
`ν ω` to be the unique probability measure satisfying
`ν ω B = E[1_{X₀∈B} | 𝒯_X](ω)` for all measurable `B`.

This requires StandardBorelSpace assumption on α to ensure existence.
-/

/-- Construction of the directing measure from conditional expectations.
For each `ω : Ω`, `ν ω` is the conditional distribution of `X₀` given the tail σ-algebra. -/
axiom directingMeasure_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ n, Measurable (X n)) :
    { ν : Ω → Measure α //
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X]) ∧
      (∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B)) }

/-! ### Step 2: Identical conditional laws -/

/-- All `X_n` have the same conditional law `ν`.
This follows from `extreme_members_equal_on_tail`. -/
lemma conditional_law_eq_directingMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν : ∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X])
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
  have h0 := hν B hB
  have hn := extreme_members_equal_on_tail hX hX_meas n B hB
  exact ae_eq_trans h0.symm hn

/-! ### Step 3: Conditional independence -/

/-- Finite-dimensional product formula for conditionally i.i.d. sequences.

**Proof strategy:**
1. Use `finite_level_factorization` to get factorization at future levels
2. Apply `tail_factorization_from_future` with reverse martingale convergence
   (`condexp_tendsto_tail`) to lift to the tail σ-algebra
3. Use identical conditional laws (from `conditional_law_eq_directingMeasure`)
   to replace each `Xᵢ` with `X₀` in the product
4. Extend from rectangles to all measurable sets via π-system/monotone class
   (rectangles generate the product σ-algebra)

This is the key step that assembles all the machinery. -/
axiom finite_product_formula
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    (m : ℕ) (k : Fin m → ℕ) :
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)

/-! ### Main theorem -/

theorem deFinetti_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X := by
  -- Step 1: Construct the directing measure ν
  obtain ⟨ν, hν_prob, hν_law, hν_meas⟩ := directingMeasure_of_contractable X hX_meas

  -- Step 2: Verify it's a ConditionallyIID certificate
  refine ⟨ν, hν_prob, ?_⟩

  -- Step 3: Prove finite-dimensional product formula
  intro m k
  exact finite_product_formula X hX hX_meas ν hν_prob hν_meas
    (fun n B hB => conditional_law_eq_directingMeasure X hX hX_meas ν hν_law n B hB) m k

end ViaMartingale
end DeFinetti
end Exchangeability
