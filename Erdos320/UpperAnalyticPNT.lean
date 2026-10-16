import Erdos320.UpperAnalyticDecay
import PrimeNumberTheoremAnd.MediumPNT

/-!
Original consequence of the Apache-licensed upstream quantitative prime number
theorem. The theorem imported here is `MediumPNT`; no analytic input is added as
an axiom or an unproved proposition.
-/

namespace Erdos320

/-- The upstream stretched-exponential PNT error is eventually bounded by any
prescribed inverse power of the logarithm, with coefficient one. -/
theorem eventual_psi_error_le_log_power (k : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |Chebyshev.psi x - x| ≤ x / Real.log x ^ k := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  obtain ⟨C, _hC, hbound⟩ := hpnt.exists_pos
  have hsmall := eventual_exp_neg_log_rpow_le_inv_log_pow k C c ((1 : ℝ) / 10)
    hc (by norm_num)
  filter_upwards [hbound.bound, hsmall, Filter.eventually_gt_atTop (1 : ℝ)]
    with x hx hsmallx hx₁
  have hx₀ : 0 ≤ x := by linarith
  have he : 0 ≤ Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := (Real.exp_pos _).le
  have hx' : |Chebyshev.psi x - x| ≤
      C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hx₀, abs_of_nonneg he] using hx
  calc
    |Chebyshev.psi x - x|
        ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := hx'
    _ = x * (C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by ring
    _ ≤ x * (1 / Real.log x ^ k) := mul_le_mul_of_nonneg_left hsmallx hx₀
    _ = x / Real.log x ^ k := by ring

end Erdos320
