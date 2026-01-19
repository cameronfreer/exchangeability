---
---

A formalization of **de Finetti's theorem** for infinite sequences on standard Borel spaces.

## Main Result

**Theorem (Kallenberg 1.1):** For an infinite sequence of random variables on a standard Borel space, the following are equivalent:

1. **(Contractable)** All strictly increasing subsequences of equal length have the same distribution
2. **(Exchangeable)** Distribution invariant under finite permutations
3. **(Conditionally i.i.d.)** Admits a directing kernel (mixture-of-products representation)

## Three Proofs

We formalize **all three proofs** from Kallenberg (2005):

| Approach | Method |
|----------|--------|
| **Martingale** | Reverse martingale convergence (Aldous) |
| **L²** | Elementary contractability bounds (ℝ-valued, L² integrable) |
| **Koopman** | Mean Ergodic Theorem |

## Visualizations

### Import Graphs

<p align="center">
  <img src="{{ site.url }}/blueprint/import_graph_colored.svg" alt="Import Graph" width="100%">
</p>

<p align="center">
  <em>Modules colored by proof: 🔵 Martingale &nbsp; 🟢 L² &nbsp; 🟠 Koopman</em>
</p>

| Graph | Description |
|-------|-------------|
| [Modules]({{ site.url }}/blueprint/import_graph_colored.html) | 57 files (interactive) |
| [All declarations]({{ site.url }}/blueprint/import_graph_full_declarations.html) | Searchable |
| [Blueprint only]({{ site.url }}/blueprint/dep_graph_document.html) | Documented items |

## Links

* [Blueprint]({{ site.url }}/blueprint/) - Proof structure with Lean links
* [Blueprint (PDF)]({{ site.url }}/blueprint/print.pdf) - Printable version
* [Documentation]({{ site.url }}/docs/) - Generated Lean documentation
* [GitHub Repository](https://github.com/cameronfreer/exchangeability)

## References

* Kallenberg, O. (2005). *Probabilistic Symmetries and Invariance Principles*. Springer. Chapter 1, Theorem 1.1.
