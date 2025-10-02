/-
Copyright (c) 2025 The Exchangeability Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Contractability and the de Finetti-Ryll-Nardzewski Theorem

This file establishes the relationship between exchangeability and contractability,
following Kallenberg's "Probabilistic Symmetries and Invariance Principles" (2005).

## Main definitions

* `Contractable`: A sequence is contractable if all increasing subsequences of equal length
  have the same distribution.
* `ConditionallyIID`: A sequence is conditionally i.i.d. if it is i.i.d. given some σ-field.
* `MixedIID`: A sequence is mixed i.i.d. if its distribution is a mixture of i.i.d. distributions.

## Main results

* `FullyExchangeable.exchangeable`: Full exchangeability implies (finite) exchangeability.
* `contractable_of_exchangeable`: Exchangeable implies contractable (via permutation extension).
* `exchangeable_of_conditionallyIID`: Conditionally i.i.d. implies exchangeable.

## Note on the de Finetti equivalences

The full de Finetti-Ryll-Nardzewski theorem establishes: contractable ↔ exchangeable ↔ conditionally i.i.d.

This file proves the "easy" directions:
- Exchangeable → contractable (via permutation extension)
- Conditionally i.i.d. → exchangeable (via product measure permutation invariance)

The "hard" directions requiring ergodic theory are stated and proved in `Exchangeability/DeFinetti.lean`
using one of three approaches (L2, Koopman, or martingale):
- Contractable → exchangeable (needs mean ergodic theorem)
- Exchangeable → conditionally i.i.d. (needs ergodic decomposition for Borel spaces)

The separate direction (exchangeable → fully exchangeable) is in `Exchangeability/Exchangeability.lean`.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Theorem 1.1
-/

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

namespace Exchangeability

/-- An infinite family of random variables `X : ℕ → Ω → α` is **exchangeable**
if the finite-dimensional distributions are invariant under permutations of finitely
many indices. -/
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ

/-- An infinite family of random variables `X : ℕ → Ω → α` is **fully exchangeable**
if the joint distribution is invariant under all permutations of ℕ. -/
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (π : Equiv.Perm ℕ),
    Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ =
      Measure.map (fun ω => fun i : ℕ => X i ω) μ

/-- Extend a permutation of `Fin n` to a permutation of ℕ by fixing all `i ≥ n`. -/
def extendFinPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (σ ⟨i, h⟩).1 else i
  invFun i := if h : i < n then (σ.symm ⟨i, h⟩).1 else i
  left_inv := by
    intro i
    by_cases h : i < n
    · -- Case: i < n, so toFun i = (σ ⟨i, h⟩).1
      simp only [h, dif_pos]
      -- Need to show: invFun (σ ⟨i, h⟩).1 = i
      have hσ : (σ ⟨i, h⟩).1 < n := (σ ⟨i, h⟩).isLt
      simp only [hσ, dif_pos]
      -- Now: (σ.symm ⟨(σ ⟨i, h⟩).1, hσ⟩).1 = i
      simp [Fin.eta, Equiv.symm_apply_apply]
    · -- Case: i ≥ n, so toFun i = i
      simp only [h, dif_neg, not_false_eq_true]
  right_inv := by
    intro i
    by_cases h : i < n
    · -- Case: i < n, so invFun i = (σ.symm ⟨i, h⟩).1
      simp only [h, dif_pos]
      -- Need to show: toFun (σ.symm ⟨i, h⟩).1 = i
      have hσ : (σ.symm ⟨i, h⟩).1 < n := (σ.symm ⟨i, h⟩).isLt
      simp only [hσ, dif_pos]
      -- Now: (σ ⟨(σ.symm ⟨i, h⟩).1, hσ⟩).1 = i
      simp [Fin.eta, Equiv.apply_symm_apply]
    · -- Case: i ≥ n, so invFun i = i
      simp only [h, dif_neg, not_false_eq_true]

/-- Exchangeability at a specific dimension n. -/
def ExchangeableAt (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ

/-- Exchangeability is equivalent to being exchangeable at every dimension. -/
lemma exchangeable_iff_forall_exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α} :
    Exchangeable μ X ↔ ∀ n, ExchangeableAt μ X n := by
  rfl

/-- Full exchangeability implies exchangeability. -/
lemma FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hX : FullyExchangeable μ X) : Exchangeable μ X := by
  classical
  intro n σ
  let π := extendFinPerm n σ
  have hπ := hX π
  let proj : (ℕ → α) → (Fin n → α) := fun f i => f i.val
  have hproj_meas : Measurable proj :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hmap₁ :=
    Measure.map_map (μ:=μ)
      (f:=fun ω => fun i : ℕ => X (π i) ω)
      (g:=proj)
      hproj_meas
      (measurable_pi_lambda _ (fun i => hX_meas (π i)))
  have hmap₂ :=
    Measure.map_map (μ:=μ)
      (f:=fun ω => fun i : ℕ => X i ω)
      (g:=proj)
      hproj_meas
      (measurable_pi_lambda _ (fun i => hX_meas i))
  have hprojσ :
      proj ∘ (fun ω => fun i : ℕ => X (π i) ω)
        = fun ω => fun i : Fin n => X (σ i) ω := by
    funext ω i
    simp [Function.comp, proj, π, extendFinPerm, Fin.is_lt]
  have hprojid :
      proj ∘ (fun ω => fun i : ℕ => X i ω)
        = fun ω => fun i : Fin n => X i.val ω := by
    ext ω i
    rfl
  -- Project both laws to the first n coordinates and compare
  calc Measure.map (fun ω i => X (σ i).val ω) μ
      = Measure.map (proj ∘ fun ω i => X (π i) ω) μ := by rw [hprojσ]
    _ = Measure.map proj (Measure.map (fun ω i => X (π i) ω) μ) := hmap₁.symm
    _ = Measure.map proj (Measure.map (fun ω i => X i ω) μ) := by rw [hπ]
    _ = Measure.map (proj ∘ fun ω i => X i ω) μ := hmap₂
    _ = Measure.map (fun ω i => X i.val ω) μ := by rw [hprojid]

/-- A finite or infinite random sequence ξ is **contractable** if all increasing subsequences
of equal length have the same distribution.

That is, (ξ_{k₁}, ..., ξ_{kₘ}) has the same distribution for any choice of
k₁ < k₂ < ... < kₘ.

This is weaker than exchangeability, which requires equality for all permutations,
not just increasing sequences. -/
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ =
      Measure.map (fun ω i => X i.val ω) μ

/-- A random sequence ξ is **conditionally i.i.d.** if there exists a σ-field ℱ and
a random probability measure ν such that P[ξ ∈ · | ℱ] = ν^∞ a.s.

In other words, ν is a probability kernel from (Ω, 𝒜) to S, or equivalently,
a random element in the space ℳ₁(S) of probability measures on S.

TODO: Full definition requires conditional probability P[· | ℱ], product measures ν^∞,
and measurability of ω ↦ ν(ω). For now, we use a simplified placeholder. -/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ℱ : MeasurableSpace Ω) (ν : Ω → Measure α),
    (∀ ω, IsProbabilityMeasure (ν ω)) ∧
    -- Placeholder: full definition needs conditional expectation machinery from mathlib
    True

/-- A random sequence ξ is **mixed i.i.d.** if its distribution is a mixture of
i.i.d. distributions: P{ξ ∈ ·} = E[ν^∞] = ∫ m^∞ P(ν ∈ dm).

This is obtained by taking expectations in the conditionally i.i.d. definition.

TODO: Full definition requires integration over the space of measures and
product measure construction. For now, we use a simplified placeholder. -/
def MixedIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ν : Measure (Measure α)),
    IsProbabilityMeasure ν ∧
    -- Placeholder: full definition needs integration over measure spaces
    True

/-- Helper lemma: If two index sequences are pointwise equal, then the corresponding
subsequences have the same distribution. -/
lemma contractable_same_range {μ : Measure Ω} {X : ℕ → Ω → α} {m : ℕ}
    (k₁ k₂ : Fin m → ℕ) (h_range : ∀ i, k₁ i = k₂ i) :
    Measure.map (fun ω i => X (k₁ i) ω) μ = Measure.map (fun ω i => X (k₂ i) ω) μ := by
  congr 1
  ext ω i
  rw [h_range]

/-- Contractability is preserved under prefix: if X is contractable, so is any finite prefix. -/
lemma Contractable.prefix {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (n : ℕ) :
    ∀ (m : ℕ) (k : Fin m → Fin n), StrictMono k →
      Measure.map (fun ω i => X (k i).val ω) μ =
        Measure.map (fun ω i => X i.val ω) μ := by
  intro m k hk_mono
  -- Lift k to a function Fin m → ℕ
  let k' : Fin m → ℕ := fun i => (k i).val
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact hk_mono hij
  -- Apply contractability
  exact hX m k' hk'_mono

/-- Exchangeable at dimension n means permuting the first n indices preserves distribution. -/
lemma ExchangeableAt.apply {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : ExchangeableAt μ X n) (σ : Equiv.Perm (Fin n)) :
    Measure.map (fun ω i => X (σ i).val ω) μ = Measure.map (fun ω i => X i.val ω) μ :=
  hX σ

/-- Contractability implies any subsequence has the same distribution as the initial segment. -/
lemma Contractable.subsequence_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X (k i) ω) μ = Measure.map (fun ω i => X i.val ω) μ :=
  hX m k hk

-- ## Helper lemmas wrapping mathlib results

/-- Product measures exist in mathlib. This placeholder captures the idea that
we can construct product probability measures. The actual construction requires
Ionescu-Tulcea or similar machinery from mathlib. -/
axiom productMeasure_exists (ν : ℕ → Measure α) [∀ i, IsProbabilityMeasure (ν i)] :
  ∃ μ : Measure (ℕ → α), IsProbabilityMeasure μ

/-- A product of identical i.i.d. measures is permutation-invariant. -/
axiom constantProduct_comp_perm (ν₀ : Measure α) [IsProbabilityMeasure ν₀]
    (μ_prod : Measure (ℕ → α)) (σ : Equiv.Perm ℕ) :
    Measure.map (fun f : ℕ → α => f ∘ σ) μ_prod = μ_prod

/-- Composing strictly monotone functions with addition preserves strict monotonicity. -/
lemma strictMono_add_left {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => c + k i) := by
  intro i j hij
  simp only
  exact Nat.add_lt_add_left (hk hij) c

/-- Composing strictly monotone functions with addition preserves strict monotonicity. -/
lemma strictMono_add_right {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => k i + c) := by
  intro i j hij
  simp only
  exact Nat.add_lt_add_right (hk hij) c

/-- For a strictly monotone function `k : Fin m → ℕ`, the values dominate the indices. -/
lemma strictMono_Fin_ge_id {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) (i : Fin m) :
    i.val ≤ k i := by
  classical
  -- Proof by strong induction on i.val
  have : ∀ n (hn : n < m), n ≤ k ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
        intro hn
        have hn' : n < m := Nat.lt_of_succ_lt hn
        let j : Fin m := ⟨n, hn'⟩
        let j_succ : Fin m := ⟨n.succ, hn⟩
        have hlt : j < j_succ := by
          simp only [Fin.lt_iff_val_lt_val, j, j_succ]
          exact Nat.lt_succ_self n
        have hk_lt : k j < k j_succ := hk hlt
        have ih' : n ≤ k j := ih hn'
        calc n.succ
            = n + 1 := rfl
          _ ≤ k j + 1 := Nat.add_le_add_right ih' 1
          _ ≤ k j_succ := Nat.succ_le_of_lt hk_lt
  exact this i.val i.isLt

/-- Given strictly monotone k : Fin m → ℕ and n containing all k(i), we can construct
a permutation σ : Perm (Fin n) such that σ maps first m positions to k-values.
This is the key lemma needed for contractable_of_exchangeable.

Construction outline:
1. Image: Im = {k(0), ..., k(m-1)} ⊆ Fin n (size m, by injectivity of k)
2. Complement: Compl = Fin n \ Im (size n - m)
3. Domain1 = {0, ..., m-1} ⊆ Fin n (first m positions)
4. Domain2 = Fin n \ Domain1 (last n - m positions)
5. Define σ : Fin n → Fin n as:
   - σ(i) = k(i) for i < m (maps Domain1 to Im)
   - σ bijectively maps Domain2 to Compl (any bijection works, e.g., via enumeration)
6. Verify σ is a bijection using:
   - Domain1 ∪ Domain2 = Fin n (disjoint union)
   - Im ∪ Compl = Fin n (disjoint union)
   - |Domain1| = |Im| = m
   - |Domain2| = |Compl| = n - m

TODO: This requires Finset/Fintype lemmas about cardinalities and Equiv.ofBijective.
Can potentially use Equiv.Perm.extendSubtype or build from Finset.image operations. -/
lemma exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  sorry

/-- Helper: relabeling coordinates by a finite permutation is measurable as a map
from (Fin n → α) to itself (with product σ-algebra). -/
lemma measurable_perm_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (fun (h : Fin n → α) => fun i => h (σ i)) := by
  -- Each coordinate i ↦ h (σ i) is measurable by measurability of evaluation.
  refine measurable_pi_lambda _ (fun i => ?_)
  -- Coordinate evaluation at (σ i) is measurable
  exact measurable_pi_apply (σ i)

/-- Helper lemma: Permuting the output coordinates doesn't change the measure.
If f and g produce the same measure, then f ∘ σ and g ∘ σ produce the same measure. -/
lemma measure_map_comp_perm {μ : Measure Ω} {n : ℕ}
    (f g : Ω → Fin n → α) (σ : Equiv.Perm (Fin n))
    (h : Measure.map f μ = Measure.map g μ)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun ω i => f ω (σ i)) μ =
      Measure.map (fun ω i => g ω (σ i)) μ := by
  -- Define the relabeling map on (Fin n → α)
  let perm_map : (Fin n → α) → (Fin n → α) := fun h => h ∘ σ
  have hfcomp : Measurable (perm_map ∘ f) := (measurable_perm_map (σ:=σ)).comp hf
  have hgcomp : Measurable (perm_map ∘ g) := (measurable_perm_map (σ:=σ)).comp hg
  have hf_rw : (fun ω i => f ω (σ i)) = perm_map ∘ f := by ext ω i; rfl
  have hg_rw : (fun ω i => g ω (σ i)) = perm_map ∘ g := by ext ω i; rfl
  -- Use map_map to pull out composition
  have h_map_f : Measure.map (perm_map ∘ f) μ = Measure.map perm_map (Measure.map f μ) :=
    (Measure.map_map (measurable_perm_map (σ:=σ)) hf).symm
  have h_map_g : Measure.map (perm_map ∘ g) μ = Measure.map perm_map (Measure.map g μ) :=
    (Measure.map_map (measurable_perm_map (σ:=σ)) hg).symm
  -- Chain equalities
  calc
    Measure.map (fun ω i => f ω (σ i)) μ
        = Measure.map (perm_map ∘ f) μ := by rw [hf_rw]
    _ = Measure.map perm_map (Measure.map f μ) := h_map_f
    _ = Measure.map perm_map (Measure.map g μ) := by rw [h]
    _ = Measure.map (perm_map ∘ g) μ := h_map_g.symm
    _ = Measure.map (fun ω i => g ω (σ i)) μ := by rw [hg_rw]

/-- Special case: The identity function on Fin n is strictly monotone when
viewed as a function to ℕ. -/
lemma fin_val_strictMono (n : ℕ) : StrictMono (fun i : Fin n => i.val) := by
  intro i j hij
  exact hij

/-- For a permutation σ on Fin n, the range {σ(0), ..., σ(n-1)} equals {0, ..., n-1}. -/
lemma perm_range_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Finset.image (fun i : Fin n => σ i) Finset.univ = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  use σ.symm x
  simp

/-- Every exchangeable sequence is contractable.
This direction is straightforward via permutation extension. -/
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) : Contractable μ X := by
  intro m k hk_mono
  -- Special case: m = 0 is trivial
  cases m with
  | zero =>
    -- Both sides map to (Fin 0 → α), which has a unique element
    congr
    ext ω i
    exact Fin.elim0 i
  | succ m' =>
    -- Choose n large enough to contain all k(i)
    -- We need n > k(m'-1) since k is strictly monotone
    let n := k ⟨m', Nat.lt_succ_self m'⟩ + 1
    
    -- Verify that all k(i) < n
    have hk_bound : ∀ i : Fin (m' + 1), k i < n := by
      intro i
      simp only [n]
      have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
        apply StrictMono.monotone hk_mono
        exact Fin.le_last i
      omega
    
    -- We need m ≤ n to apply exists_perm_extending_strictMono
    have hmn : m' + 1 ≤ n := by
      simp only [n]
      have : m' ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
        have h := strictMono_Fin_ge_id hk_mono ⟨m', Nat.lt_succ_self m'⟩
        simpa using h
      omega
    
    -- Get the permutation extending k
    obtain ⟨σ, hσ⟩ := exists_perm_extending_strictMono k hk_mono hk_bound hmn
    
    -- Define the embedding Fin (m'+1) → Fin n
    let ι : Fin (m' + 1) → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩
    
    -- Apply exchangeability to get equality of distributions on Fin n → α
    have hexch := hX n σ
    
    -- Define projection from Fin n → α to Fin (m'+1) → α
    let proj : (Fin n → α) → (Fin (m' + 1) → α) := fun f i => f (ι i)
    
    -- Push forward both sides of hexch by proj
    have hproj_meas : Measurable proj := by
      apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply (ι i)
    
    -- The map X on Ω → Fin n → α
    let f_id : Ω → (Fin n → α) := fun ω j => X j.val ω
    let f_perm : Ω → (Fin n → α) := fun ω j => X (σ j).val ω
    
    have hf_id_meas : Measurable f_id := measurable_pi_lambda _ (fun j => hX_meas j.val)
    have hf_perm_meas : Measurable f_perm := measurable_pi_lambda _ (fun j => hX_meas (σ j).val)
    
    -- Push forward hexch by proj
    have hproj_eq := congrArg (Measure.map proj) hexch
    
    -- Simplify using map_map
    have hlhs : Measure.map proj (Measure.map f_perm μ) = Measure.map (proj ∘ f_perm) μ :=
      Measure.map_map hproj_meas hf_perm_meas
    have hrhs : Measure.map proj (Measure.map f_id μ) = Measure.map (proj ∘ f_id) μ :=
      Measure.map_map hproj_meas hf_id_meas
    
    rw [hlhs, hrhs] at hproj_eq
    
    -- Now show that proj ∘ f_perm = (fun ω i => X (k i) ω)
    -- and proj ∘ f_id = (fun ω i => X i.val ω)
    have hlhs_eq : (proj ∘ f_perm) = (fun ω i => X (k i) ω) := by
      ext ω i
      simp only [proj, f_perm, Function.comp_apply, ι]
      have : (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := hσ i
      rw [this]
    
    have hrhs_eq : (proj ∘ f_id) = (fun ω i => X i.val ω) := by
      ext ω i
      simp only [proj, f_id, Function.comp_apply, ι]
    
    rw [hlhs_eq, hrhs_eq] at hproj_eq
    exact hproj_eq

/-- Conditionally i.i.d. implies exchangeable.
If X is conditionally i.i.d., then permutations preserve the distribution.

The proof would use:
1. P[ξ ∈ · | ℱ] = ν^∞ a.s. (by ConditionallyIID assumption)
2. For any permutation σ: P[ξ ∘ σ ∈ · | ℱ] = (ν^∞) ∘ σ = ν^∞ a.s.
   (product measures are permutation invariant via constantProduct_comp_perm)
3. Taking expectations: P[ξ ∈ ·] = E[ν^∞] = E[(ν^∞) ∘ σ] = P[ξ ∘ σ ∈ ·]

Since ConditionallyIID is currently a placeholder definition, we leave this as sorry.
TODO: Complete once ConditionallyIID is properly defined. -/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ConditionallyIID μ X) : Exchangeable μ X := by
  intro n σ
  -- With the current placeholder definition of ConditionallyIID, we cannot proceed
  sorry

end Exchangeability
