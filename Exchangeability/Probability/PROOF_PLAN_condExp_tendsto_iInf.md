# Proof Plan for `condExp_tendsto_iInf` (Lévy's Downward Theorem)

## Target Statement

```lean
theorem condExp_tendsto_iInf
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
  ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω))
```

## Strategy Overview

Follow the standard two-step route for reverse martingale convergence:

###

 Step A: A.S. Existence of the Limit

Treat Xₙ := μ[f | 𝔽ₙ]. For an antitone filtration, (Xₙ) is a reverse martingale:
- E[Xₙ | 𝔽ₙ₊₁] = Xₙ₊₁ (tower property, since 𝔽ₙ₊₁ ≤ 𝔽ₙ)

**Time reversal approach:**
1. For each N, define:
   - Yₙ^(N) := X_{N-n} = μ[f | 𝔽_{N-n}]
   - 𝔾ₙ^(N) := 𝔽_{N-n}
2. Then (Yₙ^(N)) is a martingale w.r.t. the increasing filtration 𝔾^(N)
3. Apply upcrossing inequality to Y^(N) (or -Y^(N)) to bound expected upcrossings
4. Crucially: the bound collapses to a constant depending only on X₀
5. Let N → ∞: deduce (Xₙ) has finitely many upcrossings/downcrossings of every rational interval
6. Conclude: (Xₙ) converges a.s. to some X∞

### Step B: Identify the Limit as μ[f | ⨅ 𝔽 n]

Let 𝔽∞ := ⨅ n, 𝔽 n and Y := μ[f | 𝔽∞]. Show X∞ = Y a.e.:

**Key observations:**

1. **Integrability and measurability:**
   - Each Xₙ is integrable and 𝔽ₙ-measurable
   - By Fatou, X∞ is integrable
   - Y is 𝔽∞-measurable and integrable

2. **Tower identities:**
   - For every n, 𝔽∞ ≤ 𝔽ₙ
   - Tower property: E[Xₙ | 𝔽∞] = E[E[f | 𝔽ₙ] | 𝔽∞] = E[f | 𝔽∞] = Y

3. **Uniform integrability of {Xₙ}:**
   - Use de la Vallée-Poussin with Φ(t) = t log(1+t)
   - Jensen for conditional expectation: Φ(|E[f | 𝔽ₙ]|) ≤ E[Φ(|f|) | 𝔽ₙ]
   - Hence: sup_n E[Φ(|Xₙ|)] ≤ E[Φ(|f|)] < ∞
   - So {Xₙ} is UI on a probability space

4. **Pass to the limit:**
   - UI + a.s. convergence ⟹ L¹ convergence: Xₙ → X∞ in L¹
   - Conditional expectation is L¹-continuous: E[Xₙ | 𝔽∞] → E[X∞ | 𝔽∞] in L¹
   - But LHS is constant sequence Y by (2), hence E[X∞ | 𝔽∞] = Y a.e.
   - Since both sides are 𝔽∞-measurable, this forces X∞ = Y a.e.

## Implementation Structure

### 1. Reverse Filtration Infrastructure (✅ DONE)

```lean
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω)

noncomputable def revCE (f : Ω → ℝ) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) : Ω → ℝ

lemma revCE_martingale : Martingale (fun n => revCE (μ := μ) f 𝔽 N n) (revFiltration 𝔽 h_antitone h_le N) μ
```

### 2. Upcrossing Bounds (TODO)

```lean
-- Uniform (in N) bound on expected upcrossings
lemma downcrossings_bdd (a b : ℝ) (h_ab : a < b) :
  ∀ N, 𝔼[upcrossings (fun n => revCE (μ := μ) f 𝔽 N n) a b] ≤ C a b f μ
```

Key: Apply mathlib's upcrossing inequality to the martingale `revCE`, using `‖μ[f | 𝔽 n]‖₁ ≤ ‖f‖₁`.

### 3. A.S. Existence of Limit (TODO)

```lean
lemma condExp_exists_ae_limit_antitone :
  ∃ X∞, (Integrable X∞ μ ∧
         ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (X∞ ω)))
```

Use uniform up/downcrossing bounds + classical convergence argument.

### 4. Uniform Integrability (TODO)

```lean
lemma uniformIntegrable_condexp_antitone :
  UniformIntegrable (fun n => μ[f | 𝔽 n]) μ
```

Proof via de la Vallée-Poussin with Φ(t) = t log(1+t) + Jensen for CE.

### 5. Limit Identification (TODO)

```lean
lemma ae_limit_is_condexp_iInf :
  ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω))
```

Steps:
1. Get a.s. limit X∞ from `condExp_exists_ae_limit_antitone`
2. UI ⟹ L¹ convergence (Vitali)
3. Pass limit through condExp at 𝔽∞ using L¹-continuity
4. Use tower identities: E[Xₙ | 𝔽∞] = E[f | 𝔽∞] for all n
5. Conclude X∞ = μ[f | 𝔽∞] a.e.

### 6. Main Theorem

```lean
theorem condExp_tendsto_iInf : -- Wrapper around ae_limit_is_condexp_iInf
```

## Required Mathlib Lemmas

### Available:
- `condExp_condExp_of_le` (tower)
- `integrable_condExp`, `ae_stronglyMeasurable_condExp`
- `eLpNorm_one_condExp_le_eLpNorm` (L¹ contraction)
- Upcrossing machinery in `Mathlib.Probability.Martingale.Convergence`

### May need to add:
- Upcrossing inequality (if not exposed)
- L¹-continuity of conditional expectation
- Uniform integrability via de la Vallée-Poussin + Jensen

## Why OrderDual Fails

Already proved in `iSup_ofAntitone_eq_F0`: For antitone F,
  ⨆ i : ℕᵒᵈ, F i.ofDual = F 0 ≠ ⨅ n, F n

Applying Lévy's upward theorem to the OrderDual filtration gives convergence to μ[f | F 0], not μ[f | ⨅ F n]. Must argue directly via reverse martingales.

## Estimation

Total implementation: ~100-200 lines

Breakdown:
- Reverse infrastructure: ✅ Done (~40 lines)
- Upcrossing bounds: ~30 lines
- A.S. existence: ~20 lines
- Uniform integrability: ~40 lines
- Limit identification: ~40 lines
- Main theorem: ~10 lines
