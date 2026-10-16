import Erdos320.UpperFinite.ResidualEstimate

/-!
The upper recursion from the classical prime-block decomposition, in the
form used by Luo, Yang, and Zhu. This is a finite combinatorial/elementary
analytic ingredient; the growing-depth asymptotic still requires proof.
-/

namespace Erdos320

theorem eventual_upper_recurrence :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
      logS N ≤ A * ((N : ℝ) / Real.log N) +
        ∑ p ∈ largePrimes N, logS (N / p) := by
  refine ⟨Real.log 4 + 216 / Real.log 2 + 8, ?_, ?_⟩
  · have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hP : ∀ p ∈ largePrimes N, 0 < p := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1.pos
    exact (finite_block_log_bound N (largePrimes N) hP).trans
      (add_le_add (residual_log_bound N hN) le_rfl)

end Erdos320
