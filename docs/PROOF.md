# Mathematical specification and proof structure

## References

1. [Erdős Problem 320](https://www.erdosproblems.com/320), with the [resolution discussion and proof claims](https://www.erdosproblems.com/forum/thread/320/proof-claims). Original reference: Erdős and Graham (1980), p. 43.
2. Luo, Yang, Zhu, [*Distinct Harmonic Subset Sums*](https://www.overleaf.com/read/ykvtbnjjppqn#2ccc1c), main theorem and Sections 2–3. The public source snapshot retrieved on 2026-10-16 UTC has SHA-256 `6472f1e013fc19e55b9ce665944c9c53cafe4c76905e9196c53dcec870a839d9` for `main.tex`; its downloaded archive has SHA-256 `6185f5d8a032b9f1b340999643fdde42426bad124cf024cba3e113b43298bb38`. The source carries no independently fixed version date. The problem site's accepted resolution is the review reference, not an assertion that the prize organizers have approved this Lean statement.
3. Bettin, Grenié, Molteni, Sanna, [arXiv:2509.10030v1](https://arxiv.org/html/2509.10030v1), Theorem 1 and its lower-bound construction.
4. Bleicher and Erdős, [*The number of distinct subsums of ∑1/i*](https://combinatorica.hu/~p_erdos/1975-45.pdf), Math. Comp. 29 (1975), 29–42; [*Denominators of Egyptian fractions. II*](https://doi.org/10.1215/ijm/1256049650), Illinois J. Math. 20 (1976), 598–613.

The target is a two-sided estimate up to positive constants. It does not assert a limiting leading constant.

## Statement correspondence

`Erdos320.sumsOf` in `Core.lean` takes the image of a finite powerset under exact rational reciprocal addition. `sums N` uses `Finset.Icc 1 N`, so denominators are positive and all subsets, including empty, occur. `S N` is the cardinality of the image, so equal sums are counted once.

`Erdos320.fullLogProduct N` in `Statement.lean` begins with `log (log N)`. Each recursive active step multiplies by one more logarithm, starting at `log₃ N`, and stops if that next factor is at most 2. `fullLogProduct_stable` proves for every `N ≥ 2` that height `N` gives the same result as every larger height. Thus the recursion is the full stopped product, not a fixed-depth surrogate. The final eventual theorem has no hypotheses and chooses its two positive constants before quantifying over all sufficiently large natural `N`.

The internal proofs use stopping threshold 3. `stopping_threshold_two_three` proves, uniformly in height and input, that the threshold-2 product lies between the threshold-3 product and three times that product. `problemScale_comparison` and `Erdos320.erdos_320` apply this proved comparison to obtain the exact manuscript convention.

## Original Lean proof

The following describes the implemented proof and its organization. It is not a substitute for kernel checking.

### Upper bound

`UpperRecurrence` proves the finite prime-block decomposition. An arbitrary finite cover bounds the sumset cardinality by the product of block cardinalities. Dilation by a prime identifies the block contribution with a smaller reciprocal-subsum problem. A common denominator for the residual block gives an absolute multiple of `N / log N` after taking logarithms.

The `UpperAnalytic*` modules derive uniform prime-interval estimates from the pinned upstream quantitative `MediumPNT`. The shrinking error is proved to have vanishing product with `log₃ N`. No prime-counting hypothesis remains in the final application.

The normalized entropy is controlled by a running maximum. The first three cofactor blocks enter an absolute constant. The remaining kernel starts at four; its integral leaves the strictly positive reserve `log (log 3)`. This reserve absorbs the vanishing prime-interval error before multiplying by the running maximum and preserves coefficient one at each iteration. A strong-induction invariant yields the full growing-depth product bound. `Erdos320.eventual_upper_bound` in `UpperAnalyticFinal.lean` closes every analytic and finite input.

### Lower bound

`LowerFinite` and `LowerArithmetic` prove exact doubling for an independent denominator and the compatible-prime extension by rational numerator/denominator arithmetic. `LowerCompatible`, `LowerMultiplication`, and `LowerCounting` turn those extensions into an injective disjoint counting construction. The explicit cutoff is bounded in `LowerCutoff` and `LowerCutoffGrowth`.

`PrimeCounting`, `PrimeCountingEventual`, and `LowerRenewal` discharge uniform prime differences from the proved PNT input, then establish an actual discrete renewal inequality for the independent-denominator count, with a positive baseline and its required moving endpoint. A finite Abel summation supplies the needed weighted count.

`LowerAnalytic` proves a general renewal implication. Its depth-dependent losses are summable, and their coefficient product stays uniformly positive. Adaptive cutoffs and a finite reciprocal-log mesh permit induction over every depth; comparison at the maximal admissible depth recovers the full stopped product with one fixed positive constant. `Erdos320.eventual_lower_bound` in `Lower.lean` applies this result to the actual denominator construction and converts exact doubling to a lower bound on `log S`.

`Erdos320.two_sided_estimate` combines the two complete bounds. `Erdos320.erdos_320` supplies the exact threshold-2 conclusion. There are no undeclared analytic inputs in this chain.
