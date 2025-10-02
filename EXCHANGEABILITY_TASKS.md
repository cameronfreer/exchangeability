# Exchangeability Roadmap

This document tracks medium-sized formalisation efforts that grew out of the
current exchangeability development. Treat each item as a mini-project: when an
entry is finished, either delete it or replace it with a short note pointing to
the final Lean statements.

## Project A — Extending Finite Permutations to `ℕ`

**Goal.** Given a finite permutation on `Fin n`, build an accompanying
`Equiv.Perm ℕ` that agrees on the first `n` indices and is the identity
elsewhere. The intended Lean proof will likely use `Equiv.Perm.extendDomain`
against the inclusion `Fin n ↪ ℕ` and a complementary equivalence on the
remaining indices.

**Why it matters.** The exchangeable ⇒ fully exchangeable direction in
`Exchangeability.lean` currently stalls while constructing this permutation.
Supplying a reusable lemma (with clean API and measurability facts) would
unblock that proof and could simplify other arguments about finitely supported
permutations.

**Notes.**

- Decide on an idiomatic embedding `ι : Fin n ↪ ℕ` (probably `Fin.castLE` with
  a proof that `n ≤ m`).
- Provide helper lemmas for recovering the action on `Fin n` and confirming the
  extended permutation fixes indices outside the support.
- Keep the final statement agnostic over the target type so it can live in
  `Mathlib` if desired.

## Project B — Kolmogorov π–λ Uniqueness for Product Laws

**Goal.** Show that two probability measures on `(ℕ → α)` coincide once their
finite-dimensional marginals agree. Formally, if pushforwards along every
projection `ℕ → Fin n` match, then the measures themselves are equal.

**Why it matters.** This is the second missing piece for the Kolmogorov-style
argument in `Exchangeability.lean`. Proving the theorem inside the project (or
abstracting it into a reusable lemmas) will complete the “exchangeable implies
fully exchangeable” result without resorting to `sorry` placeholders.

**Notes.**

- The intended proof uses Dynkin’s π–λ theorem on cylinder sets.
- Confirm whether Mathlib already exposes a variant; adapt if possible.
- Package the result so it can apply to general index sets (not just `ℕ`) in
  case future developments need that flexibility.

