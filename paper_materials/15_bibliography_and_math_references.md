---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Bibliography and Mathematical References

## Primary Source

### Kallenberg (2005)

**Full citation:**
> Kallenberg, Olav. *Probabilistic Symmetries and Invariance Principles*. Probability and Its Applications. Springer, New York, 2005. xii+510 pp. ISBN: 0-387-25115-4.
> MR2161313 (2006i:60002)

**Relevant sections:**
- **Theorem 1.1** (page 26-28): The main de Finetti-Ryll-Nardzewski equivalence
- **Lemma 1.2** (page 27): L² correlation bound for contractable sequences
- **Lemma 1.3** (page 27): Contraction-independence lemma
- **First proof** (page 26): Koopman operator approach
- **Second proof** (page 27): Elementary L² bounds
- **Third proof** (page 28): Reverse martingale approach

---

## Secondary Sources

### Aldous (1983)

**Full citation:**
> Aldous, David J. *Exchangeability and related topics*. École d'Été de Probabilités de Saint-Flour XIII—1983, 1–198, Lecture Notes in Math., 1117, Springer, Berlin, 1985.
> MR0883646 (88d:60107)

**Relevance:** Comprehensive survey including martingale proof of de Finetti's theorem.

---

### de Finetti (1931)

**Full citation:**
> de Finetti, Bruno. *Funzione caratteristica di un fenomeno aleatorio*. Atti della R. Academia Nazionale dei Lincei, Ser. 6. Memorie, Classe di Scienze Fisiche, Matematiche e Naturali, 4 (1931), 251–299.

**Relevance:** Original statement of de Finetti's theorem for 0-1 valued sequences.

---

### de Finetti (1937)

**Full citation:**
> de Finetti, Bruno. *La prévision: ses lois logiques, ses sources subjectives*. Ann. Inst. H. Poincaré, 7 (1937), 1–68.

**Relevance:** Extended version with philosophical foundations.

---

### Ryll-Nardzewski (1957)

**Full citation:**
> Ryll-Nardzewski, Czesław. *On stationary sequences of random variables and the de Finetti's equivalence*. Colloq. Math., 4 (1957), 149–156.
> MR0088823 (19,585a)

**Relevance:** Extended de Finetti's theorem to general state spaces using ergodic theory.

---

### Hewitt-Savage (1955)

**Full citation:**
> Hewitt, Edwin and Savage, Leonard J. *Symmetric measures on Cartesian products*. Trans. Amer. Math. Soc., 80 (1955), 470–501.
> MR0076206 (17,863g)

**Relevance:** Measure-theoretic treatment of symmetric (exchangeable) measures.

---

### Kallenberg (2002)

**Full citation:**
> Kallenberg, Olav. *Foundations of Modern Probability*. Second edition. Probability and Its Applications. Springer-Verlag, New York, 2002. xx+638 pp. ISBN: 0-387-95313-2.
> MR1876169 (2002m:60002)

**Relevant sections:**
- **Theorem 11.10**: de Finetti's theorem
- **Chapter 10**: Stationary Processes and Ergodic Theory (FMP 10.2-10.4)

---

### Diaconis-Freedman (1980)

**Full citation:**
> Diaconis, Persi and Freedman, David. *Finite exchangeable sequences*. Ann. Probab., 8 (1980), no. 4, 745–764.
> MR0577313 (81m:60032)

**Relevance:** Finite versions of de Finetti's theorem.

---

## mathlib References

### Measure Theory

- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
- `Mathlib.MeasureTheory.Constructions.Pi`
- `Mathlib.MeasureTheory.PiSystem`

### Conditional Expectation

- `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`
- `Mathlib.Probability.ConditionalExpectation`

### Probability Kernels

- `Mathlib.Probability.Kernel.Basic`
- `Mathlib.Probability.Kernel.CondDistrib`
- `Mathlib.Probability.Kernel.Condexp`

### Martingales

- `Mathlib.Probability.Martingale.Basic`
- `Mathlib.Probability.Martingale.Convergence`

### Ergodic Theory

- `Mathlib.Dynamics.Ergodic.MeasurePreserving`
- `Mathlib.Dynamics.Ergodic.Ergodic`

---

## Theorem Attributions

| Theorem | Attribution | Year |
|---------|-------------|------|
| de Finetti's theorem (0-1 case) | de Finetti | 1931 |
| de Finetti's theorem (general) | Ryll-Nardzewski, Hewitt-Savage | 1955-57 |
| Contraction-independence lemma | Aldous (Lemma 1.3 in Kallenberg) | 1983 |
| L² correlation bound | Kallenberg (Lemma 1.2) | 2005 |
| Martingale proof | Aldous, Kallenberg "Third proof" | 1983, 2005 |
| Koopman proof | Kallenberg "First proof" | 2005 |
| Elementary L² proof | Kallenberg "Second proof" | 2005 |

---

## BibTeX Entries

```bibtex
@book{kallenberg2005,
  author = {Kallenberg, Olav},
  title = {Probabilistic Symmetries and Invariance Principles},
  series = {Probability and Its Applications},
  publisher = {Springer},
  address = {New York},
  year = {2005},
  pages = {xii+510},
  isbn = {0-387-25115-4},
  mrnumber = {2161313}
}

@incollection{aldous1985,
  author = {Aldous, David J.},
  title = {Exchangeability and related topics},
  booktitle = {École d'Été de Probabilités de Saint-Flour XIII—1983},
  series = {Lecture Notes in Math.},
  volume = {1117},
  pages = {1--198},
  publisher = {Springer},
  address = {Berlin},
  year = {1985},
  mrnumber = {883646}
}

@article{ryllnardzewski1957,
  author = {Ryll-Nardzewski, Czesław},
  title = {On stationary sequences of random variables and the de {F}inetti's equivalence},
  journal = {Colloq. Math.},
  volume = {4},
  year = {1957},
  pages = {149--156},
  mrnumber = {88823}
}
```
