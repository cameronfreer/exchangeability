import LeantestAfp.Probability.DeFinetti
import LeantestAfp.Probability.Ergodic.KoopmanMeanErgodic
import LeantestAfp.Probability.DeFinetti.InvariantSigma
import LeantestAfp.Probability.DeFinetti.MeanErgodicStep

/-!
This project is centred on the formalisation of de Finetti's theorem.  The
`LeantestAfp` library currently re-exports the probability namespace containing
the statement and supporting scaffolding for the result.

## New modules (Mean Ergodic approach)

The mean-ergodic proof of de Finetti (following Kallenberg 2005) is developed in:
- `Probability.Ergodic.KoopmanMeanErgodic`: Koopman operator and Mean Ergodic Theorem
- `Probability.DeFinetti.InvariantSigma`: Shift-invariant σ-algebra and projection = condexp
- `Probability.DeFinetti.MeanErgodicStep`: Cylinder functions and main convergence results
-/
