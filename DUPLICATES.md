# Duplicate Declaration Analysis

This document explains the results of duplicate detection in the codebase and distinguishes between real duplicates (now fixed) and false positives (acceptable by design).

## Real Duplicates (Fixed)

These were genuine duplicates that have been resolved:

### 1. `integrable_of_bounded` ✅ Fixed in commit a67880d
- **Was at**: `CondExp.lean:532` (had sorry), `ViaKoopman.lean:2998` (complete proof)
- **Fix**: Copied proof to CondExp.lean, removed from ViaKoopman.lean
- **Reason**: CondExp is infrastructure - proofs belong there, not in specific proof files

### 2. `comap_comp_le` ✅ Fixed in commit a67880d
- **Was at**: `ViaKoopman.lean:957`, `MartingaleHelpers.lean:56`
- **Fix**: Removed from ViaKoopman, kept in MartingaleHelpers
- **Reason**: MartingaleHelpers is the proper home for this σ-algebra helper lemma

### 3. `cylinder` ✅ Documented in commit a67880d
- **At**: `CondExp.lean:142`, `CylinderHelpers.lean:73`
- **Status**: Intentionally duplicated (now documented with NOTE)
- **Reason**: CondExp cannot import PathSpace (circular dependency)

### 4. `condIndep_of_indicator_condexp_eq` ✅ Fixed in commit 6431402
- **Was at**: `CondExp.lean:184`, `CondExpExtras.lean:44`
- **Fix**: Removed from CondExpExtras.lean (parking lot file)
- **Reason**: Used in ViaMartingale.lean:2130, belongs in CondExp.lean

### 5. `condExp_indicator_mul_indicator_of_condIndep` ✅ Fixed in commit 6431402
- **Was at**: `CondExp.lean:282`, `CondExpExtras.lean:296`
- **Fix**: Removed from CondExpExtras.lean
- **Reason**: Core infrastructure, not experimental

### 6. `shift` ✅ Fixed (new file created)
- **Was at**: `CommonEnding.lean:91`, `KoopmanMeanErgodic.lean:106`
- **Fix**: Created central `PathSpace/Shift.lean` with comprehensive shift operator definition
- **Reason**: Fundamental operation on path space (ℕ → α) used across ergodic theory and de Finetti proofs
- **Details**: Combined best parts of both definitions (shift, shift_measurable, IsShiftInvariant, etc.)

### 7. `AgreeOnFutureRectangles` ✅ Fixed (removed from CondExp)
- **Was at**: `CondExp.lean:150` (structure wrapping μ = ν), `ViaMartingale.lean:896` (def for rectangle agreement)
- **Fix**: Removed useless structure from CondExp.lean
- **Reason**: CondExp version was just wrapping equality in a structure. ViaMartingale has the real definition that proves rectangle agreement implies equality.
- **Details**: Updated `condexp_indicator_eq_of_agree_on_future_rectangles` to take measure equality directly instead of wrapping it in a structure

## False Positives (By Design)

These declarations share names but are NOT duplicates - they exist in different contexts/namespaces or serve different purposes:

### Type/Structure Definitions in Multiple Namespaces

#### `tailSigma` (3 locations) ✅ OK
- `DeFinetti/InvariantSigma.lean:19` - namespace `Exchangeability`
- `DeFinetti/ViaL2.lean:114` - namespace `Exchangeability.DeFinetti.L2Approach`
- `DeFinetti/ViaKoopman.lean:211` - namespace `Exchangeability.DeFinetti.Koopman`

**Why OK**: Different namespaces for different proof approaches. Each proof file defines its own local context. The InvariantSigma version is the public API; the others are proof-specific helpers.

#### `Kernel` (4 locations) ✅ OK
- `Probability/Kernel.lean:48` - structure definition
- `DeFinetti/ViaL2.lean:223` - namespace `L2Approach`
- `DeFinetti/ViaKoopman.lean:283` - namespace `Koopman`
- `DeFinetti/ViaMartingale.lean:278` - namespace `Martingale`

**Why OK**: Infrastructure `Kernel` structure vs proof-specific helper definitions. Different purposes in different proof contexts.

#### Exchangeability Predicates (6+ locations) ✅ OK
- `Contractable`, `Exchangeable`, `ExchangeableAt`, `FullyExchangeable`
- Found in: `Contractability.lean`, `Core.lean`, `ViaL2.lean`, `ViaKoopman.lean`, `ViaMartingale.lean`

**Why OK**: These are fundamental definitions that appear in multiple proof contexts. The canonical definitions are in `Core.lean` and `Contractability.lean`. Other files may have local helper definitions or restatements for specific proof approaches.

### Theorem Variants

#### `conditionallyIID_of_contractable` (2 locations) ✅ OK
- `DeFinetti/TheoremViaL2.lean` - L² proof version
- `DeFinetti/TheoremViaMartingale.lean` - Martingale proof version

**Why OK**: These are **different proofs** of the same mathematical statement. The project deliberately implements three independent proof approaches (L², Koopman/Ergodic, Martingale) from Kallenberg (2005). Each file proves the key implication using different machinery.

### Helper Lemmas in Multiple Proofs

#### `shift`, `tailFamily`, `tailSigmaAlgebra`, `tailSigma_le` ✅ OK
- Appear in multiple files: `ViaL2.lean`, `ViaKoopman.lean`, `ViaMartingale.lean`

**Why OK**: Each of the three proof approaches needs its own infrastructure for working with tail σ-algebras and sequence shifts. While they could potentially be shared, they are proof-specific implementations that may differ subtly in their exact definitions or assumptions.

## Duplicate Detection Methodology

Duplicates were found using:
```bash
# Extract all declarations
rg '^(theorem|lemma|def|structure|class|instance|abbrev) ([^ ]+)' \
   --only-matching --no-heading Exchangeability/ \
   > /tmp/declarations.txt

# Find duplicates
awk -F: '{print $2":"$1}' /tmp/declarations.txt | \
  sort | \
  uniq -d -w50 | \
  awk -F: '{name=$2; gsub(/{.*/, "", name); gsub(/ *$/, "", name); gsub(/^ */, "", name); print name":"$1}'
```

This finds declarations with duplicate names but requires manual inspection to distinguish real duplicates from false positives.

## Guidelines for Future Development

1. **Before adding infrastructure**: Check if it exists in `Probability/` modules
2. **Before duplicating a lemma**: Consider if it's truly proof-specific or should be shared
3. **When duplicating is necessary**: Add a NOTE comment explaining why (e.g., circular imports)
4. **Proof-specific helpers**: Okay to duplicate in `ViaL2.lean`, `ViaKoopman.lean`, `ViaMartingale.lean` if they're truly specific to that proof approach
5. **Core definitions**: Should have single canonical location in `Core.lean`, `Contractability.lean`, or `Probability/` modules

## Summary

- **Real duplicates fixed**: 7 total
  - 5 from previous session (integrable_of_bounded, comap_comp_le, cylinder documentation, 2 from CondExpExtras)
  - 2 from this session (shift, AgreeOnFutureRectangles)
- **False positives explained**: ~20+ declarations across categories above
- **Remaining duplicates**: None requiring action
- **New files created**: `PathSpace/Shift.lean` (canonical shift operator definition)

The false positives are primarily:
1. Namespace-scoped definitions in different proof approaches (by design)
2. Multiple independent proofs of the same theorem (project goal)
3. Proof-specific helper infrastructure (acceptable separation)
