---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Curated Snippet Library

## Category 1: Core Definitions

**Snippet 1: Exchangeable**
- Path: `Exchangeability/Contractability.lean`
- Lines: 81-84
- Purpose: Define finite-permutation invariance for infinite sequences

```lean
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ
```

*Math translation:* A sequence is exchangeable iff for every n and permutation σ of {0,...,n-1}, the joint law of (X_{σ(0)}, ..., X_{σ(n-1)}) equals that of (X_0, ..., X_{n-1}).

---

**Snippet 2: Contractable**
- Path: `Exchangeability/Contractability.lean`
- Lines: 199-202
- Purpose: Define strictly-monotone subsequence invariance

```lean
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ =
      Measure.map (fun ω i => X i.val ω) μ
```

*Math translation:* For every strictly increasing k: {0,...,m-1} → ℕ, the law of (X_{k(0)}, ..., X_{k(m-1)}) equals that of (X_0, ..., X_{m-1}).

---

**Snippet 3: ConditionallyIID**
- Path: `Exchangeability/ConditionallyIID.lean`
- Lines: 140-150
- Purpose: Existence of directing measure with product structure

```lean
structure ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop where
  ν : Ω → Measure α
  isProb : ∀ ω, IsProbabilityMeasure (ν ω)
  measurable_eval : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => (ν ω) B)
  finite_product : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ =
      μ.bind (fun ω => Measure.pi (fun _ => ν ω))
```

*Math translation:* There exists a kernel ν such that Law(X_k) = ∫ ν(ω)^⊗m dμ(ω).

---

## Category 2: Main Theorems

**Snippet 4: de Finetti's Theorem**
- Path: `Exchangeability/DeFinetti/TheoremViaMartingale.lean`
- Lines: 96-103
- Purpose: Main theorem statement

```lean
theorem deFinetti
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X :=
  conditionallyIID_of_contractable X hX_meas (contractable_of_exchangeable hX_exch hX_meas)
```

*Math translation:* For standard Borel spaces, Exchangeable ⇒ ConditionallyIID.

---

**Snippet 5: Full Equivalence**
- Path: `Exchangeability/DeFinetti/TheoremViaMartingale.lean`
- Lines: 138-153
- Purpose: Kallenberg Theorem 1.1

```lean
theorem deFinetti_RyllNardzewski_equivalence
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · intro hContract
    have hCIID := conditionallyIID_of_contractable X hX_meas hContract
    have hExch := exchangeable_of_conditionallyIID hX_meas hCIID
    exact ⟨hExch, hCIID⟩
  · intro ⟨hExch, _⟩
    exact contractable_of_exchangeable hExch hX_meas
```

*Math translation:* Contractable ⟺ Exchangeable ⟺ Conditionally i.i.d.

---

## Category 3: Easy Directions

**Snippet 6: Exchangeable → Contractable**
- Path: `Exchangeability/Contractability.lean`
- Lines: 486-535
- Purpose: Permutation extension argument

```lean
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) : Contractable μ X := by
  intro m k hk_mono
  cases m with
  | zero => congr; ext ω i; exact Fin.elim0 i
  | succ m' =>
    let last : Fin (m' + 1) := ⟨m', Nat.lt_succ_self m'⟩
    let n := k last + 1
    obtain ⟨σ, hσ⟩ := exists_perm_extending_strictMono k hk_mono (hk_bound) hmn
    -- Apply exchangeability and project
    ...
```

*Math translation:* Extend k to a permutation σ, apply exchangeability, project.

---

**Snippet 7: ConditionallyIID → Exchangeable**
- Path: `Exchangeability/ConditionallyIID.lean`
- Lines: 260-280
- Purpose: Product measures are permutation-invariant

```lean
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hCIID : ConditionallyIID μ X) :
    Exchangeable μ X := by
  intro n σ
  -- Product measures are permutation-invariant
  have hpi : ∀ ν : Measure α, Measure.map (· ∘ σ) (Measure.pi (fun _ : Fin n => ν)) =
      Measure.pi (fun _ => ν) := pi_comp_perm
  -- Apply finite_product and permutation invariance
  ...
```

*Math translation:* ν^⊗n is permutation-invariant, so Law(X ∘ σ) = Law(X).

---

## Category 4: Key Combinatorial Lemmas

**Snippet 8: Permutation Extension**
- Path: `Exchangeability/Contractability.lean`
- Lines: 313-370
- Purpose: Extend strictly monotone k to permutation

```lean
lemma exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  classical
  let e : {x : Fin n // x.val < m} ≃ {x : Fin n // ∃ i, x = ⟨k i, hk_bound i⟩} := ...
  let σ := Equiv.extendSubtype e
  ...
```

*Math translation:* Any injective k: Fin m → Fin n with m ≤ n extends to a permutation.

---

## Category 5: Directing Measure Construction

**Snippet 9: Directing Measure (Martingale)**
- Path: `Exchangeability/DeFinetti/ViaMartingale/DirectingMeasure.lean`
- Lines: ~50-80
- Purpose: Construct ν via conditional distribution kernel

```lean
def directingMeasure
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) : Ω → Measure α :=
  condExpKernel μ (X 0) (tailSigma X)
```

*Math translation:* ν(ω) = Law(X_0 | tail σ-algebra)(ω).

---

## Category 6: π-System Extension

**Snippet 10: Prefix Cylinders**
- Path: `Exchangeability/Core.lean`
- Lines: 76-96
- Purpose: Define cylinder sets

```lean
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i

def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α) :=
  (prefixProj α n) ⁻¹' S
```

*Math translation:* {ω | (ω_0, ..., ω_{n-1}) ∈ S}.

---

**Snippet 11: Measure Extension**
- Path: `Exchangeability/Core.lean`
- Lines: ~200-230
- Purpose: π-system uniqueness

```lean
theorem measure_eq_of_fin_marginals_eq
    {μ ν : Measure (ℕ → α)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n S, MeasurableSet S → μ (prefixCylinder S) = ν (prefixCylinder S)) :
    μ = ν
```

*Math translation:* Two finite measures agreeing on all cylinders are equal.

---

## Category 7: Tail σ-Algebra

**Snippet 12: Tail Shift**
- Path: `Exchangeability/Tail/TailSigma.lean`
- Lines: ~20-40
- Purpose: Define tail σ-algebra

```lean
def tailShift (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  ⨅ n : ℕ, MeasurableSpace.comap (shift^[n]) inferInstance
```

*Math translation:* ℱ_∞ = ⋂_n σ(X_n, X_{n+1}, ...).

---

## Category 8: Ergodic Theory

**Snippet 13: Koopman Operator**
- Path: `Exchangeability/Ergodic/KoopmanMeanErgodic.lean`
- Lines: ~50-70
- Purpose: Define Koopman operator on L²

```lean
def koopmanOp (T : Ω → Ω) (hT : MeasurePreserving T μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  compRightCLM hT
```

*Math translation:* (U_T f)(ω) = f(Tω).

---

**Snippet 14: Mean Ergodic Theorem**
- Path: `Exchangeability/Ergodic/KoopmanMeanErgodic.lean`
- Lines: ~150-180
- Purpose: Cesàro averages converge to invariant projection

```lean
theorem mean_ergodic_L2
    (T : Ω → Ω) (hT : MeasurePreserving T μ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (1 : ℝ) / n • ∑ i ∈ Finset.range n, koopmanOp T hT^i f)
      atTop (𝓝 (invariantProjection T hT f))
```

*Math translation:* (1/n) Σ U^i f → P f in L².

---

## Category 9: L² Bounds

**Snippet 15: Block Average**
- Path: `Exchangeability/DeFinetti/ViaL2/BlockAverages.lean`
- Lines: ~50-70
- Purpose: Define Cesàro average

```lean
def blockAvg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (1 / n) * ∑ i ∈ Finset.range n, X i ω
```

*Math translation:* α_n(ω) = (1/n) Σ_{i=0}^{n-1} X_i(ω).

---

## Category 10: Conditional Independence

**Snippet 16: Contraction Independence (Kallenberg 1.3)**
- Path: `Exchangeability/Probability/CondIndep/KallenbergIndicator.lean`
- Lines: ~100-150
- Purpose: Core lemma for martingale proof

```lean
theorem condIndep_of_contraction
    (hLaw : Measure.map (Y, W) μ = Measure.map (Y, W') μ)
    (hSub : (⟨σ(W), ⋯⟩ : MeasurableSpace Ω) ≤ ⟨σ(W'), ⋯⟩) :
    CondIndep μ Y W' ⟨σ(W), ⋯⟩
```

*Math translation:* If (Y,W) =^d (Y,W') and σ(W) ⊆ σ(W'), then Y ⊥⊥_W W'.

---

## Summary

| Category | Snippets | Key Files |
|----------|----------|-----------|
| Definitions | 3 | Contractability.lean, ConditionallyIID.lean |
| Main theorems | 2 | TheoremViaMartingale.lean |
| Easy directions | 2 | Contractability.lean, ConditionallyIID.lean |
| Combinatorics | 1 | Contractability.lean |
| Directing measure | 1 | DirectingMeasure.lean |
| π-system | 2 | Core.lean |
| Tail σ-algebra | 1 | TailSigma.lean |
| Ergodic theory | 2 | KoopmanMeanErgodic.lean |
| L² bounds | 1 | BlockAverages.lean |
| Cond. independence | 1 | KallenbergIndicator.lean |
