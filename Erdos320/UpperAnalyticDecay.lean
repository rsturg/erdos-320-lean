import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Original elementary decay estimates used to turn the quantitative prime number
theorem into a polynomial logarithmic endpoint error.
-/

namespace Erdos320

/-- A stretched exponential in `log x` beats every fixed power of `log x`. -/
theorem tendsto_log_pow_mul_exp_neg_rpow
    (k : ℕ) (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Filter.Tendsto
      (fun x : ℝ => Real.log x ^ k * Real.exp (-c * Real.log x ^ r))
      Filter.atTop (nhds 0) := by
  have hinner : Filter.Tendsto (fun x : ℝ => Real.log x ^ r)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop
  have houter :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / r) c hc
  refine (houter.comp hinner).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hpow : (Real.log x ^ r) ^ ((k : ℝ) / r) = Real.log x ^ k := by
    rw [← Real.rpow_mul hl, mul_div_cancel₀ _ hr.ne', Real.rpow_natCast]
  simp only [Function.comp_apply, hpow]

theorem eventual_exp_neg_log_rpow_le_inv_log_pow
    (k : ℕ) (C c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ x : ℝ in Filter.atTop,
      C * Real.exp (-c * Real.log x ^ r) ≤ 1 / Real.log x ^ k := by
  have hlim : Filter.Tendsto
      (fun x : ℝ => C * (Real.log x ^ k * Real.exp (-c * Real.log x ^ r)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_log_pow_mul_exp_neg_rpow k c r hc hr).const_mul C
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop,
      C * (Real.log x ^ k * Real.exp (-c * Real.log x ^ r)) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hxl
  apply (le_div_iff₀ (pow_pos (Real.log_pos hxl) k)).mpr
  nlinarith only [hx.le]

end Erdos320
