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

/-! ### Cons and Tail Operations -/

/-- Cons a value onto a sequence: `consRV x t` produces `[x, t(0), t(1), ...]`. -/
def consRV (x : Ω → α) (t : Ω → ℕ → α) : Ω → ℕ → α
| ω, 0 => x ω
| ω, (n+1) => t ω n

/-- Tail of a sequence: drops index 0, so `tailRV t n = t (n+1)`. -/
def tailRV (t : Ω → ℕ → α) : Ω → ℕ → α := fun ω n => t ω (n+1)

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma tailRV_consRV (x : Ω → α) (t : Ω → ℕ → α) : tailRV (consRV x t) = t := rfl

/-! ### Measurability -/

/-! ### Measurable combinators -/

/-- A process viewed as a full path is measurable. -/
@[measurability, fun_prop]
lemma measurable_path {X : ℕ → Ω → α} (hX : ∀ n, Measurable (X n)) : Measurable (path X) := by
  unfold path; fun_prop

/-- Consing a head to a sequence is measurable if both pieces are measurable. -/
@[measurability, fun_prop]
lemma measurable_consRV (x : Ω → α) (t : Ω → ℕ → α) :
    Measurable x → Measurable t → Measurable (consRV x t) := by
  intro hx ht
  refine measurable_pi_lambda _ ?_
  intro n; cases n <;> simp [consRV] <;> fun_prop

omit [MeasurableSpace Ω] in
/-- The contraction property: σ(tailRV t) ≤ σ(t).

This is the key property for Kallenberg 1.3: tail gives a coarser σ-algebra. -/
@[nolint unusedArguments]
lemma comap_tailRV_le {t : Ω → ℕ → α} :
    MeasurableSpace.comap (tailRV t) inferInstance ≤
    MeasurableSpace.comap t inferInstance := by
  have hShift : Measurable (fun s : ℕ → α => (fun n => s (n + 1))) := by
    fun_prop
  intro S hS
  obtain ⟨A, hA, rfl⟩ := hS
  exact ⟨(fun s : ℕ → α => (fun n => s (n + 1)) ) ⁻¹' A, hA.preimage hShift, rfl⟩

omit [MeasurableSpace Ω] in
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
  simpa [shiftRV, path] using (measurable_path (fun n => hX (m + n)))

end Exchangeability.DeFinetti.ViaMartingale
