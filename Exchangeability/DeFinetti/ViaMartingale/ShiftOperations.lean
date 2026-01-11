/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability
import Exchangeability.Tail.TailSigma
import Exchangeability.DeFinetti.MartingaleHelpers

/-!
# Shift Operations for Martingale Proof

Core definitions for sequence shifting and tail operations used throughout the
ViaMartingale proof:

* `path X` - The random path ω ↦ (n ↦ X n ω)
* `shiftRV X m` - Shifted path ω ↦ (n ↦ X (m + n) ω)
* `shiftProcess X m` - Shifted process (θₘX)ₙ = X_{m+n}
* `consRV`, `tailRV` - Cons and tail for sequences

These are extracted from ViaMartingale.lean to enable modular imports.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Path and Shift Definitions -/

/-- The random path of a process: ω ↦ (n ↦ X n ω). -/
def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

/-- Shifted random path: ω ↦ (n ↦ X (m + n) ω). -/
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

/-- Shifted process: (θₘX)ₙ = X_{m+n}. -/
def shiftProcess (X : ℕ → Ω → α) (m : ℕ) : ℕ → Ω → α := fun n ω => X (m + n) ω

/-! ### Cons and Tail Operations -/

/-- Cons a value onto a sequence: `consRV x t` produces `[x, t(0), t(1), ...]`. -/
def consRV (x : Ω → α) (t : Ω → ℕ → α) : Ω → ℕ → α
| ω, 0 => x ω
| ω, (n+1) => t ω n

/-- Tail of a sequence: drops index 0, so `tailRV t n = t (n+1)`. -/
def tailRV (t : Ω → ℕ → α) : Ω → ℕ → α := fun ω n => t ω (n+1)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma consRV_zero (x : Ω → α) (t : Ω → ℕ → α) (ω : Ω) : consRV x t ω 0 = x ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma consRV_succ (x : Ω → α) (t : Ω → ℕ → α) (ω : Ω) (n : ℕ) :
    consRV x t ω (n+1) = t ω n := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma tailRV_apply (t : Ω → ℕ → α) (ω : Ω) (n : ℕ) : tailRV t ω n = t ω (n+1) := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma tailRV_consRV (x : Ω → α) (t : Ω → ℕ → α) : tailRV (consRV x t) = t := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftRV_apply (X : ℕ → Ω → α) (m ω n) :
    shiftRV X m ω n = X (m + n) ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftRV_zero (X : ℕ → Ω → α) : shiftRV X 0 = path X := by
  ext ω n; simp [shiftRV, path]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftProcess_apply (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) :
    shiftProcess X m n ω = X (m + n) ω := rfl

/-! ### Measurability -/

/-- Tail is measurable when the original sequence is measurable. -/
lemma measurable_tailRV {t : Ω → ℕ → α} (ht : Measurable t) : Measurable (tailRV t) :=
  measurable_pi_iff.mpr fun n => (measurable_pi_apply (n + 1)).comp ht

/-- The contraction property: σ(tailRV t) ≤ σ(t).

This is the key property for Kallenberg 1.3: tail gives a coarser σ-algebra. -/
@[nolint unusedArguments]
lemma comap_tailRV_le {t : Ω → ℕ → α} :
    MeasurableSpace.comap (tailRV t) inferInstance ≤
    MeasurableSpace.comap t inferInstance := by
  intro S hS
  obtain ⟨A, hA, rfl⟩ := hS
  exact ⟨(fun s : ℕ → α => (fun n => s (n+1))) ⁻¹' A,
    hA.preimage (measurable_pi_iff.mpr fun n => measurable_pi_apply (n + 1)), rfl⟩

/-- For W' = consRV x W, we have σ(W) ≤ σ(W').

This is the contraction for Kallenberg 1.3 when W' = cons(X_r, W). -/
@[nolint unusedArguments]
lemma comap_le_comap_consRV (x : Ω → α) (t : Ω → ℕ → α) :
    MeasurableSpace.comap t inferInstance ≤
    MeasurableSpace.comap (consRV x t) inferInstance := by
  calc MeasurableSpace.comap t inferInstance
      = MeasurableSpace.comap (tailRV (consRV x t)) inferInstance := by
        simp only [tailRV_consRV]
    _ ≤ MeasurableSpace.comap (consRV x t) inferInstance := comap_tailRV_le

variable {X : ℕ → Ω → α}

@[measurability, fun_prop]
lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) {m : ℕ} :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

/-! ### Shift Contractability -/

/-- If `X` is contractable, then so is each of its shifts `θₘ X`. -/
lemma shift_contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) : Contractable μ (shiftProcess X m) := by
  intro n k hk_mono
  let k' : Fin n → ℕ := fun i => m + k i
  have hk'_mono : StrictMono k' := fun i j hij => Nat.add_lt_add_left (hk_mono hij) m
  let j : Fin n → ℕ := fun i => m + i
  have hj_mono : StrictMono j := fun i₁ i₂ h => Nat.add_lt_add_left h m
  have h1 := hX n k' hk'_mono
  have h2 := hX n j hj_mono
  calc Measure.map (fun ω i => shiftProcess X m (k i) ω) μ
      = Measure.map (fun ω i => X (k' i) ω) μ := rfl
    _ = Measure.map (fun ω i => X i.val ω) μ := h1
    _ = Measure.map (fun ω i => X (j i) ω) μ := h2.symm
    _ = Measure.map (fun ω i => shiftProcess X m i.val ω) μ := rfl

end Exchangeability.DeFinetti.ViaMartingale
