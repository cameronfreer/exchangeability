---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Core Definitions

## Exchangeable

**File:** `Exchangeability/Contractability.lean:81`

```lean
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ
```

**Mathematical definition:** A sequence `(X₀, X₁, X₂, ...)` is *exchangeable* if for every `n ∈ ℕ` and every permutation `σ` of `{0, 1, ..., n-1}`:

```
(X_{σ(0)}, X_{σ(1)}, ..., X_{σ(n-1)}) =ᵈ (X₀, X₁, ..., X_{n-1})
```

where `=ᵈ` denotes equality in distribution.

**Intuition:** The joint distribution is invariant under any finite reordering of indices.

**Example:** Successive draws from an urn with replacement, where the replacement mechanism may depend on the composition.

---

## FullyExchangeable

**File:** `Exchangeability/Contractability.lean:96`

```lean
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (π : Equiv.Perm ℕ),
    Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ =
      Measure.map (fun ω => fun i : ℕ => X i ω) μ
```

**Mathematical definition:** The sequence is invariant under *all* permutations of ℕ, not just finite ones.

**Relationship:** For probability measures on standard Borel spaces:
```
FullyExchangeable ⟺ Exchangeable
```

This equivalence uses π-system uniqueness.

---

## Contractable

**File:** `Exchangeability/Contractability.lean:199`

```lean
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ =
      Measure.map (fun ω i => X i.val ω) μ
```

**Mathematical definition:** A sequence is *contractable* if for every `m ∈ ℕ` and every strictly increasing function `k : {0, ..., m-1} → ℕ`:

```
(X_{k(0)}, X_{k(1)}, ..., X_{k(m-1)}) =ᵈ (X₀, X₁, ..., X_{m-1})
```

**Intuition:** Any "thinned" subsequence (indices in increasing order) has the same distribution as the initial segment of the same length.

**Example:** For i.i.d. sequences, any increasing subsequence `(X₂, X₅, X₁₇)` has the same joint distribution as `(X₀, X₁, X₂)`.

**Key property:** Contractability is *weaker* than exchangeability in general, but equivalent for infinite sequences on standard Borel spaces.

---

## ConditionallyIID

**File:** `Exchangeability/ConditionallyIID.lean:190`

```lean
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → Measure α,
    (∀ ω, IsProbabilityMeasure (ν ω)) ∧
    (∀ B, MeasurableSet B → Measurable (fun ω => ν ω B)) ∧
      ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
          = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)
```

**Mathematical definition:** There exists a random probability measure `ν : Ω → Measure α` (the *directing measure*) such that:

1. For each `ω`, `ν(ω)` is a probability measure on `α`
2. The map `ω ↦ ν(ω)(B)` is measurable for each measurable `B`
3. For all strictly increasing `k`:
   ```
   Law(X_{k(0)}, ..., X_{k(m-1)}) = ∫ ν(ω)^⊗m dμ(ω)
   ```

**Note:** This is a `def` (existential statement), not a `structure`. The proof of de Finetti's theorem constructs the directing measure `ν` explicitly.

**Intuition:** "Conditionally on `ν`, the sequence is i.i.d. with distribution `ν`."

**Alternative phrasing:** The finite-dimensional distributions are mixtures of product measures.

---

## Relationship Diagram

```
                    ┌─────────────┐
                    │Exchangeable │
                    └──────┬──────┘
                           │ contractable_of_exchangeable
                           ▼
                    ┌─────────────┐
                    │ Contractable│
                    └──────┬──────┘
                           │ conditionallyIID_of_contractable
                           ▼
                    ┌──────────────────┐
                    │ ConditionallyIID │
                    └────────┬─────────┘
                             │ exchangeable_of_conditionallyIID
                             ▼
                    ┌─────────────┐
                    │Exchangeable │ (closes the loop)
                    └─────────────┘
```

For infinite sequences on standard Borel spaces, all three are equivalent.

---

## Easy Directions

### Exchangeable → Contractable

**Proof idea:** Given a strictly increasing `k : Fin m → ℕ`, extend it to a permutation `σ` of `Fin n` for large enough `n`. Exchangeability gives invariance under `σ`, then project to the first `m` coordinates.

**Key lemma:** `exists_perm_extending_strictMono`

```lean
lemma exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, _⟩).val = k i
```

### ConditionallyIID → Exchangeable

**Proof idea:** Product measures are permutation-invariant. If `X` is conditionally i.i.d. with distribution `ν`, then:

```
Law(X_{σ(0)}, ..., X_{σ(n-1)}) = ∫ ν^⊗n dμ = Law(X₀, ..., X_{n-1})
```

**Key lemma:** `pi_comp_perm` (product measures are permutation-invariant)

---

## Type-Theoretic Notes

1. **Universe polymorphism:** All definitions are universe-polymorphic in `Ω` and `α`.

2. **Measurability:** We require `[MeasurableSpace Ω]` and `[MeasurableSpace α]` as instance arguments.

3. **Standard Borel:** The full equivalence requires `[StandardBorelSpace Ω]` and `[StandardBorelSpace α]` for the hard direction.

4. **Strictness:** `StrictMono k` means `k i < k j` whenever `i < j` (strictly increasing), not just weakly increasing.
