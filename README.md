# Erdős Problem 320 in Lean 4

An original, AI-assisted formalization conducted for **Riley Sturgill**, with **jenw1n (Jensen Kohlmeyer)** credited as project co-author. See [ATTRIBUTION.md](ATTRIBUTION.md) for the evidenced roles and mathematical credits.

The target is the complete order-of-magnitude resolution of [Erdős Problem 320](https://www.erdosproblems.com/320), catalogued as [JSP-000266](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#jsp-000266--how-many-distinct-subset-sums-do-the-reciprocals-of-the-first-several-positive-integers-have).

Let

\[
S(N)=\left|\left\{\sum_{n\in A}\frac1n:A\subseteq\{1,\ldots,N\}\right\}\right|,
\qquad
L_2(N)=\prod_{\substack{j\ge3\\\log_j N>2}}\log_j N,
\]

where the product stops at the first factor at most two, and an empty product is one. The theorem proves that there are absolute constants \(c,C>0\) such that, for every sufficiently large natural number \(N\),

\[
c\frac{N}{\log N}L_2(N)\le\log S(N)\le C\frac{N}{\log N}L_2(N).
\]

The fully qualified result is **`Erdos320.erdos_320`**, in [Erdos320/Final.lean](Erdos320/Final.lean). All subset sums are exact rational numbers, and the empty subset is included. [Statement.lean](Erdos320/Statement.lean) proves that the finite recursion used for the iterated-log product has enough height to include every required factor. The constants are chosen before the eventual quantifier; the depth grows with the input.

## Reproduce

The project pins Lean **4.31.0**, Mathlib **`db127794c79fdeb86f6b0cf6ff2c804026fbaff1`**, and every dependency through [lake-manifest.json](lake-manifest.json). The quantitative prime-number theorem comes from the separately licensed upstream [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6739793850d3eaa031e3543ed72d7f026f8080f5), not an assumed analytic estimate.

With Git, Python 3, and [elan](https://github.com/leanprover/elan) available:

```sh
git clone https://github.com/rsturg/erdos-320-lean.git
cd erdos-320-lean
# Check out the full commit named in the submission before verification.
lake env lean --version
python scripts/fetch_mathlib_cache.py
lake build
python scripts/audit.py --lean --fingerprints verification/source-fingerprints.json
```

Keep the committed lockfile; `lake update` selects a different dependency state. The cache helper fetches the 82-root import cone used in the fresh verification, reducing disk use. See [docs/VERIFICATION.md](docs/VERIFICATION.md) for the recorded release verification, exact audit commands, and limitations. [docs/DEPENDENCIES.md](docs/DEPENDENCIES.md) documents dependency provenance and licenses.

The final theorem's transitive axiom report is:

```text
'Erdos320.erdos_320' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard propositional extensionality, classical choice, and quotient soundness axioms. The submitted proof has no placeholder proof steps or added unproved mathematical assumptions.

## Sources and prize status

The mathematical resolution is credited to Yanping Luo, Ruiyi Yang, and Keheng Zhu, *Distinct Harmonic Subset Sums*, with the lower-bound work of Sandro Bettin, Loïc Grenié, Giuseppe Molteni, and Carlo Sanna. The manuscript discloses AI assistance. Historical work by Bleicher and Erdős is also credited. Exact references and the formal proof structure are in [docs/PROOF.md](docs/PROOF.md).

This repository is an independently developed formal proof. Earlier public formalizations and pending prize submissions exist; [docs/PRIOR_WORK.md](docs/PRIOR_WORK.md) discloses the evidence. Publication and a successful build do not establish first-formalizer priority, prize eligibility, or an award. The committee must resolve those questions. [docs/SUBMISSION.md](docs/SUBMISSION.md) records the submission and the remaining contributor-only claim steps.

Original project source is released under Apache-2.0; dependencies retain their own licenses.
