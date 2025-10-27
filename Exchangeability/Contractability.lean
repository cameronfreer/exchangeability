/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Exchangeability.Probability.InfiniteProduct
import Exchangeability.Util.StrictMono

/-!
# Contractability and Exchangeability

This file establishes the relationship between **exchangeability** and **contractability**
for infinite sequences of random variables, following Kallenberg's "Probabilistic
Symmetries and Invariance Principles" (2005).

## Main definitions

* `Exchangeable μ X`: The sequence `X` is exchangeable under measure `μ` if its
  finite-dimensional distributions are invariant under finite permutations.
* `FullyExchangeable μ X`: The sequence is fully exchangeable if invariant under
  *all* permutations of ℕ (not just finite ones).
* `Contractable μ X`: The sequence is contractable if all strictly increasing
  subsequences of equal length have the same distribution.

## Main results

* `FullyExchangeable.exchangeable`: Full exchangeability implies (finite) exchangeability.
* `contractable_of_exchangeable`: **Exchangeable ⇒ contractable** (via permutation extension).
* `exists_perm_extending_strictMono`: Key combinatorial lemma showing that any strictly
  monotone function `k : Fin m → ℕ` can be extended to a permutation of `Fin n`.

## The de Finetti-Ryll-Nardzewski equivalence

The full theorem establishes the equivalence for infinite sequences:
  **contractable ↔ exchangeable ↔ conditionally i.i.d.**

This file proves the implication **exchangeable → contractable** using a permutation
extension argument.

### The complete picture

- **Exchangeable → contractable** (this file): Any strictly increasing subsequence
  can be realized as the image of the first m coordinates under some permutation.
- **Contractable → exchangeable** (`Exchangeability/DeFinetti/*.lean`): Uses ergodic
  theory and the martingale convergence approach.
- **Exchangeable ↔ fully exchangeable** (`Exchangeability/Exchangeability.lean`):
  Uses π-system uniqueness and finite approximation of infinite permutations.
- **Conditionally i.i.d. → exchangeable** (`Exchangeability/ConditionallyIID.lean`):
  Directly from the definition.

## Implementation notes

The key technical challenge is constructing permutations that extend strictly monotone
selections. Given `k : Fin m → ℕ` with `k(0) < k(1) < ... < k(m-1)`, we construct
a permutation `σ : Perm (Fin n)` such that `σ(i) = k(i)` for `i < m`. This uses
`Equiv.extendSubtype` to extend a bijection between subtypes to a full permutation.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Theorem 1.1
* Kallenberg, "Foundations of Modern Probability" (2002), Theorem 11.10
-/

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

namespace Exchangeability

/--
A sequence of random variables is **exchangeable** if permuting finitely many indices
preserves the joint distribution.

Formally, for every `n` and every permutation `σ` of `Fin n`, the distribution of
`(X_{σ(0)}, ..., X_{σ(n-1)})` equals the distribution of `(X_0, ..., X_{n-1})`.

This is the central notion in de Finetti's theorem.
-/
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ

/--
A sequence is **fully exchangeable** if permuting *any* indices preserves the distribution.

This is stronger than `Exchangeable` because it requires invariance under *all*
permutations of ℕ, not just finite ones. However, `Exchangeability.lean` proves
that these notions are equivalent for probability measures.

Formally, for every permutation `π : Perm ℕ`, the distribution of the reindexed
sequence `(X_{π(0)}, X_{π(1)}, ...)` equals the distribution of `(X_0, X_1, ...)`.
-/
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (π : Equiv.Perm ℕ),
    Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ =
      Measure.map (fun ω => fun i : ℕ => X i ω) μ

/--
Extend a finite permutation to a permutation of ℕ by fixing points ≥ n.

Given a permutation `σ` of `Fin n`, this produces a permutation of ℕ that acts
as σ on `{0, ..., n-1}` and fixes all `i ≥ n`.

This is used to connect full exchangeability with finite exchangeability.
-/
def extendFinPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (σ ⟨i, h⟩).1 else i
  invFun i := if h : i < n then (σ.symm ⟨i, h⟩).1 else i
  left_inv i := by
    by_cases h : i < n <;> simp [h, Fin.eta, Equiv.symm_apply_apply]
  right_inv i := by
    by_cases h : i < n <;> simp [h, Fin.eta, Equiv.apply_symm_apply]

/-- Exchangeability at a specific dimension n. -/
def ExchangeableAt (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ

/-- Exchangeability is equivalent to being exchangeable at every dimension. -/
lemma exchangeable_iff_forall_exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α} :
    Exchangeable μ X ↔ ∀ n, ExchangeableAt μ X n := by
  rfl

/--
Full exchangeability implies exchangeability.

If a sequence is invariant under all permutations of ℕ, it is certainly invariant
under finite permutations. The proof uses `extendFinPerm` to view a finite
permutation as an infinite one.
-/
lemma FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hX : FullyExchangeable μ X) : Exchangeable μ X := by
  classical
  intro n σ
  let π := extendFinPerm σ
  have hπ := hX π
  let proj : (ℕ → α) → (Fin n → α) := fun f i => f i.val
  have hproj_meas : Measurable proj := by measurability
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

/-- Exchangeability is preserved under composition of permutations. -/
lemma Exchangeable.comp {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : Exchangeable μ X) (σ τ : Equiv.Perm (Fin n)) :
    Measure.map (fun ω i => X ((σ.trans τ) i).val ω) μ =
      Measure.map (fun ω i => X i.val ω) μ :=
  hX n (σ.trans τ)

/-- The identity permutation preserves the distribution (trivially). -/
lemma Exchangeable.refl {μ : Measure Ω} {X : ℕ → Ω → α} (n : ℕ) :
    Measure.map (fun ω (i : Fin n) => X (Equiv.refl (Fin n) i).val ω) μ =
      Measure.map (fun ω (i : Fin n) => X i.val ω) μ := by
  congr

/--
A sequence is **contractable** if all strictly increasing subsequences of equal
length have the same distribution.

**Definition:** For any `m` and any strictly increasing function `k : Fin m → ℕ`,
the distribution of `(X_{k(0)}, ..., X_{k(m-1)})` equals the distribution of
`(X_0, ..., X_{m-1})`.

**Intuition:** Contractability is weaker than exchangeability. While exchangeability
requires invariance under all permutations, contractability only requires invariance
under "order-preserving selections" - we can choose any m indices as long as they
are in increasing order.

**Example:** For i.i.d. sequences, any increasing subsequence has the same
distribution as the initial segment, so contractability holds.

This is a key property in de Finetti's theorem, equivalent to both exchangeability
and conditional independence.
-/
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ =
      Measure.map (fun ω i => X i.val ω) μ

/-- Helper lemma: If two index sequences are pointwise equal, then the corresponding
subsequences have the same distribution. -/
lemma contractable_same_range {μ : Measure Ω} {X : ℕ → Ω → α} {m : ℕ}
    (k₁ k₂ : Fin m → ℕ) (h_range : ∀ i, k₁ i = k₂ i) :
    Measure.map (fun ω i => X (k₁ i) ω) μ = Measure.map (fun ω i => X (k₂ i) ω) μ := by
  congr 1; ext ω i; rw [h_range]

/-- Contractability is preserved under prefix: if X is contractable, so is any finite prefix. -/
lemma Contractable.prefix {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (n : ℕ) :
    ∀ (m : ℕ) (k : Fin m → Fin n), StrictMono k →
      Measure.map (fun ω i => X (k i).val ω) μ =
        Measure.map (fun ω i => X i.val ω) μ := by
  intro m k hk_mono
  exact hX m (fun i => (k i).val) (fun i j hij => hk_mono hij)

/-- Exchangeable at dimension n means permuting the first n indices preserves distribution. -/
lemma ExchangeableAt.apply {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : ExchangeableAt μ X n) (σ : Equiv.Perm (Fin n)) :
    Measure.map (fun ω i => X (σ i).val ω) μ = Measure.map (fun ω i => X i.val ω) μ :=
  hX σ

/--
Contractability implies any strictly increasing subsequence matches the initial segment.

This is just a restatement of the definition for clarity.
-/
lemma Contractable.subsequence_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X (k i) ω) μ = Measure.map (fun ω i => X i.val ω) μ :=
  hX m k hk

/--
Any two strictly increasing subsequences of the same length have equal distributions.

For a contractable sequence, `(X_{k₁(0)}, ..., X_{k₁(m-1)})` and
`(X_{k₂(0)}, ..., X_{k₂(m-1)})` have the same distribution whenever both `k₁` and
`k₂` are strictly increasing, regardless of which specific indices are chosen.

This is the key property that makes contractability useful: the distribution
depends only on the length of the subsequence, not on which increasing subsequence
is selected.
-/
lemma Contractable.allStrictMono_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) (k₁ k₂ : Fin m → ℕ)
    (hk₁ : StrictMono k₁) (hk₂ : StrictMono k₂) :
    Measure.map (fun ω i => X (k₁ i) ω) μ = Measure.map (fun ω i => X (k₂ i) ω) μ :=
  (hX m k₁ hk₁).trans (hX m k₂ hk₂).symm

/-- Contractability implies that the distribution is determined by the marginal distributions
of increasing selections. -/
lemma Contractable.determined_by_increasing {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) :
    ∀ m : ℕ, ∃! ν : Measure (Fin m → α),
      ∀ k : Fin m → ℕ, StrictMono k →
        Measure.map (fun ω i => X (k i) ω) μ = ν := by
  intro m
  use Measure.map (fun ω i => X i.val ω) μ
  constructor
  · intro k hk; exact hX m k hk
  · intro ν' hν'; exact (hν' (fun i => i.val) (fun i j hij => hij)).symm

/-- Contractability is symmetric: if (X_{k(0)}, ..., X_{k(m-1)}) has the same distribution
as the initial segment, then the converse also holds. -/
lemma Contractable.symm {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X i.val ω) μ = Measure.map (fun ω i => X (k i) ω) μ :=
  (hX m k hk).symm

/-- The infinite i.i.d. product measure exists for any probability measure.
Constructed via Ionescu-Tulcea in `Exchangeability.Probability.InfiniteProduct`. -/
lemma iidProduct_exists {ν₀ : Measure α} [IsProbabilityMeasure ν₀] :
    ∃ μ : Measure (ℕ → α), IsProbabilityMeasure μ :=
  ⟨Exchangeability.Probability.iidProduct ν₀, inferInstance⟩

/-- The i.i.d. product of identical measures is permutation-invariant.
This is a consequence of the construction via Ionescu-Tulcea. -/
lemma iidProduct_perm_invariant {ν₀ : Measure α} [IsProbabilityMeasure ν₀]
    (σ : Equiv.Perm ℕ) :
    Measure.map (fun f : ℕ → α => f ∘ σ)
      (Exchangeability.Probability.iidProduct ν₀) =
      Exchangeability.Probability.iidProduct ν₀ :=
  Exchangeability.Probability.iidProduct.perm_eq (ν:=ν₀) (σ:=σ)

-- Re-export StrictMono utilities for backward compatibility
open Util.StrictMono (strictMono_add_left strictMono_add_right
                       strictMono_Fin_ge_id fin_val_strictMono strictMono_comp)

/--
Any strictly increasing function can be extended to a permutation.

**Statement:** Given a strictly increasing `k : Fin m → ℕ` with all values `< n`
and `m ≤ n`, there exists a permutation `σ : Perm (Fin n)` such that
`σ(i) = k(i)` for all `i < m`.

**Intuition:** We want to build a permutation that "realizes" the selection `k`
as the image of the first `m` positions. Since `k` is strictly increasing, it's
injective, so its image has cardinality `m`. We can extend this to a full
permutation by arbitrarily pairing up the remaining elements.

**Construction outline:**
1. **Domain partition:** `{0,...,m-1}` ∪ `{m,...,n-1}` = `Fin n`
2. **Codomain partition:** `{k(0),...,k(m-1)}` ∪ `complement` = `Fin n`
3. Map first `m` positions to `k`-values: `σ(i) = k(i)` for `i < m`
4. Extend arbitrarily to remaining positions using `Equiv.extendSubtype`

This is the key combinatorial lemma enabling `contractable_of_exchangeable`:
any strictly increasing subsequence can be realized via a permutation.
-/
lemma exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  classical
  -- Embed `Fin m` into `Fin n` via the initial segment.
  let ι : Fin m → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩
  let p : Fin n → Prop := fun x => x.val < m
  let q : Fin n → Prop := fun x => ∃ i : Fin m, x = ⟨k i, hk_bound i⟩
  have hι_mem : ∀ i : Fin m, p (ι i) := by
    intro i
    dsimp [p, ι]
    exact i.isLt
  let kFin : Fin m → Fin n := fun i => ⟨k i, hk_bound i⟩
  have hk_mem : ∀ i : Fin m, q (kFin i) := fun i => ⟨i, rfl⟩
  haveI : DecidablePred p := fun x => inferInstance
  haveI : DecidablePred q := fun x => inferInstance
  -- Equivalence between the first `m` coordinates and `Fin m`.
  let e_dom : {x : Fin n // p x} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      , invFun := fun i => ⟨ι i, by
          dsimp [p, ι]
          exact i.isLt⟩
      , left_inv := by
          rintro ⟨x, hx⟩
          ext; simp [ι]
      , right_inv := by
          intro i
          cases i with
          | mk i hi =>
            simp [ι] }
  -- Equivalence between the image of `k` and `Fin m`.
  -- For injectivity of k, we use that it's strictly monotone
  have hk_inj : Function.Injective kFin := by
    intro i j hij
    have : k i = k j := by
      have := Fin.ext_iff.mp hij
      simpa [kFin] using this
    exact hk_mono.injective this
  let e_cod : Fin m ≃ {x : Fin n // q x} :=
    { toFun := fun i => ⟨kFin i, hk_mem i⟩
      , invFun := fun y => Classical.choose y.2
      , left_inv := by
          intro i
          have h_spec := Classical.choose_spec (hk_mem i)
          have : k (Classical.choose (hk_mem i)) = k i := by
            simpa [kFin] using (Fin.ext_iff.mp h_spec).symm
          exact hk_mono.injective this
      , right_inv := by
          rintro ⟨y, hy⟩
          apply Subtype.ext
          simp only [kFin]
          exact (Classical.choose_spec hy).symm }
  -- Equivalence between the subtypes describing the first `m` coordinates and the image of `k`.
  let e : {x : Fin n // p x} ≃ {x : Fin n // q x} := e_dom.trans e_cod
  -- Extend this equivalence to a permutation of `Fin n`.
  let σ : Equiv.Perm (Fin n) := Equiv.extendSubtype e
  have hσ_apply : ∀ i : Fin m, σ (ι i) = kFin i := by
    intro i
    have hmem : p (ι i) := hι_mem i
    have h_apply := Equiv.extendSubtype_apply_of_mem (e:=e) (x:=ι i) hmem
    -- Evaluate the right-hand side explicitly.
    dsimp [σ, e, Equiv.trans, e_dom, e_cod, ι, Fin.castLEEmb, kFin] at h_apply
    simpa using h_apply
  refine ⟨σ, ?_⟩
  intro i
  have hi_eq : (⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩ : Fin n) = ι i := by
    apply Fin.ext
    simp [ι]
  have hσ_val : (σ (ι i)).val = k i := by
    have := congrArg Fin.val (hσ_apply i)
    simpa [kFin] using this
  simpa [hi_eq] using hσ_val

/-- Helper: relabeling coordinates by a finite permutation is measurable as a map
from (Fin n → α) to itself (with product σ-algebra). -/
lemma measurable_perm_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (fun (h : Fin n → α) => fun i => h (σ i)) := by
  measurability

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
  calc Measure.map (fun ω i => f ω (σ i)) μ
      = Measure.map perm_map (Measure.map f μ) := by
        rw [show (fun ω i => f ω (σ i)) = perm_map ∘ f by ext; rfl]
        exact (Measure.map_map (measurable_perm_map (σ:=σ)) hf).symm
    _ = Measure.map perm_map (Measure.map g μ) := by rw [h]
    _ = Measure.map (fun ω i => g ω (σ i)) μ := by
        rw [show (fun ω i => g ω (σ i)) = perm_map ∘ g by ext; rfl]
        exact Measure.map_map (measurable_perm_map (σ:=σ)) hg

/-- Contractability implies the first m variables have the same joint distribution
regardless of which m consecutive variables we pick (starting from position k). -/
lemma Contractable.shift_segment_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m k : ℕ) :
    Measure.map (fun ω (i : Fin m) => X (k + i.val) ω) μ =
      Measure.map (fun ω (i : Fin m) => X i.val ω) μ := by
  exact hX m (fun i => k + i.val) (fun i j hij => Nat.add_lt_add_left hij k)

/-- Contractable sequences are invariant under taking strictly increasing subsequences
with offsets. -/
lemma Contractable.shift_and_select {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) (k : Fin m → ℕ) (offset : ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X (offset + k i) ω) μ =
      Measure.map (fun ω i => X i.val ω) μ := by
  exact hX m (fun i => offset + k i) (fun i j hij => Nat.add_lt_add_left (hk hij) offset)

/-- For a permutation σ on Fin n, the range {σ(0), ..., σ(n-1)} equals {0, ..., n-1}. -/
lemma perm_range_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset.image (fun i : Fin n => σ i) Finset.univ = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  use σ.symm x
  simp

/--
**Main theorem:** Every exchangeable sequence is contractable.

**Statement:** If `X` is exchangeable, then any strictly increasing subsequence
has the same distribution as the initial segment.

**Proof strategy:**
1. Given a strictly increasing `k : Fin m → ℕ`, choose `n` large enough to
   contain all `k(i)` values.
2. Use `exists_perm_extending_strictMono` to construct a permutation `σ : Perm (Fin n)`
   such that `σ(i) = k(i)` for `i < m`.
3. Apply exchangeability: the distributions under `σ` and the identity are equal.
4. Project both sides to the first `m` coordinates to conclude that
   `(X_{k(0)}, ..., X_{k(m-1)})` has the same distribution as `(X_0, ..., X_{m-1})`.

**Mathematical significance:** This shows that exchangeability (invariance under
all finite permutations) implies contractability (invariance under increasing
selections). The converse requires ergodic theory and is much deeper.

This is one direction of de Finetti's theorem.
-/
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
      have : m' ≤ k ⟨m', Nat.lt_succ_self m'⟩ :=
        strictMono_Fin_ge_id hk_mono ⟨m', Nat.lt_succ_self m'⟩
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
    have hproj_meas : Measurable proj :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (ι i))

    -- The map X on Ω → Fin n → α
    let f_id : Ω → (Fin n → α) := fun ω j => X j.val ω
    let f_perm : Ω → (Fin n → α) := fun ω j => X (σ j).val ω

    have hf_id_meas : Measurable f_id := measurable_pi_lambda _ (fun j => hX_meas j.val)
    have hf_perm_meas : Measurable f_perm := measurable_pi_lambda _ (fun j => hX_meas (σ j).val)

    -- Combine: push forward hexch by proj and simplify using map_map
    have hproj_eq : Measure.map (proj ∘ f_perm) μ = Measure.map (proj ∘ f_id) μ := by
      rw [← Measure.map_map hproj_meas hf_perm_meas,
          ← Measure.map_map hproj_meas hf_id_meas]
      exact congrArg (Measure.map proj) hexch
    
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

end Exchangeability
