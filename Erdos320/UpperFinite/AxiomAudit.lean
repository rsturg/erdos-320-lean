import Erdos320.UpperRecurrence

example : ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
    Erdos320.logS N ≤ A * ((N : ℝ) / Real.log N) +
      ∑ p ∈ Erdos320.largePrimes N, Erdos320.logS (N / p) :=
  Erdos320.eventual_upper_recurrence

#print axioms Erdos320.eventual_upper_recurrence
#print axioms Erdos320.finite_block_product_bound
#print axioms Erdos320.residual_log_bound
