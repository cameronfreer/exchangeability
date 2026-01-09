---
usemathjax: true
---

# Exchangeability in Lean 4

A formalization of **de Finetti's theorem** and the **de Finetti--Ryll-Nardzewski equivalence** for infinite sequences on Borel spaces.

## Main Result

**Theorem (Kallenberg 1.1):** For an infinite sequence of random variables on a Borel space, the following are equivalent:

1. **(Contractable)** All strictly increasing subsequences of equal length have the same distribution
2. **(Exchangeable)** Distribution invariant under finite permutations
3. **(Conditionally i.i.d.)** Coordinates are i.i.d. given the tail $\sigma$-algebra

## Three Independent Proofs

We formalize **all three proofs** from Kallenberg (2005):

| Approach | Method | Status |
|----------|--------|--------|
| **Martingale** | Reverse martingale convergence (Aldous) | Complete |
| **L$^2$** | Elementary contractability bounds | Complete |
| **Koopman** | Mean Ergodic Theorem | Complete |

## Links

* [Blueprint]({{ site.url }}/blueprint/) - Proof structure with Lean links
* [Blueprint (PDF)]({{ site.url }}/blueprint.pdf)
* [Dependency Graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [API Documentation]({{ site.url }}/docs/)
* [GitHub Repository](https://github.com/cameronfreer/exchangeability)

## References

* Kallenberg, O. (2005). *Probabilistic Symmetries and Invariance Principles*. Springer. Chapter 1, Theorem 1.1.
