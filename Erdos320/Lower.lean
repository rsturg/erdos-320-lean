import Erdos320.LowerRenewal
import Erdos320.LowerAnalytic.Renewal

/-!
The complete lower bound for the full growing-depth scale. The counting
construction, prime estimates, discrete renewal, and uniform-depth iteration
are all supplied by proved declarations in the imported modules.
-/

namespace Erdos320

open Filter

theorem eventual_lower_bound_of_count
    (hcount : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * scale N ≤ independentCount N) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * scale N ≤ logS N := by
  obtain ⟨c, hc, hcount⟩ := hcount
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨c * Real.log 2, mul_pos hc hlog2, ?_⟩
  filter_upwards [hcount] with N hN
  calc
    (c * Real.log 2) * scale N = (c * scale N) * Real.log 2 := by ring
    _ ≤ independentCount N * Real.log 2 := mul_le_mul_of_nonneg_right hN hlog2.le
    _ ≤ logS N := independentCount_log_lower N

theorem eventual_independent_full_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * scale N ≤ independentCount N :=
  LowerAnalytic.eventual_lower_from_renewal independentCount lowerCofactorBound
    (1 / 2) (by norm_num) eventual_independent_prime_baseline
    eventual_independent_lower_recurrence eventual_independent_lower_endpoint

/-- The unconditional lower half of the complete Erdős Problem 320 estimate. -/
theorem eventual_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * scale N ≤ logS N :=
  eventual_lower_bound_of_count eventual_independent_full_lower

end Erdos320
