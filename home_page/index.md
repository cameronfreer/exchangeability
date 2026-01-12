---
---

A formalization of **de Finetti's theorem** for infinite sequences on standard Borel spaces.

## Main Result

**Theorem (Kallenberg 1.1):** For an infinite sequence of random variables on a Borel space, the following are equivalent:

1. **(Contractable)** All strictly increasing subsequences of equal length have the same distribution
2. **(Exchangeable)** Distribution invariant under finite permutations
3. **(Conditionally i.i.d.)** Coordinates are i.i.d. given the tail σ-algebra

## Three Proofs

We formalize **all three proofs** from Kallenberg (2005):

| Approach | Method |
|----------|--------|
| **Martingale** | Reverse martingale convergence (Aldous) |
| **L²** | Elementary contractability bounds |
| **Koopman** | Mean Ergodic Theorem |

## Visualizations

### Import Graphs

<p align="center">
  <img src="{{ site.url }}/blueprint/import_graph_colored.svg" alt="Import Graph" width="100%">
</p>

<p align="center">
  <em>Color legend: 🔵 ViaMartingale &nbsp; 🟢 ViaL2 &nbsp; 🟠 ViaKoopman</em>
</p>

| Graph | Description |
|-------|-------------|
| [File-level Import Graph]({{ site.url }}/blueprint/import_graph_colored.html) | Interactive graph of 57 files with physics simulation |
| [Declaration-level Graph]({{ site.url }}/blueprint/import_graph_full_declarations.html) | All 431 declarations with search functionality |
| [Mathematical Dependency Graph]({{ site.url }}/blueprint/dep_graph_document.html) | Blueprint proof structure |

## Links

* [Blueprint]({{ site.url }}/blueprint/) - Proof structure with Lean links
* [Blueprint (PDF)]({{ site.url }}/blueprint/print.pdf) - Printable version
* [Documentation]({{ site.url }}/docs/) - Generated Lean documentation
* [GitHub Repository](https://github.com/cameronfreer/exchangeability)

## References

* Kallenberg, O. (2005). *Probabilistic Symmetries and Invariance Principles*. Springer. Chapter 1, Theorem 1.1.
