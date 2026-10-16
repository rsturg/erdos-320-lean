import Erdos320.LogProduct
import Mathlib.Algebra.Order.Floor.Semiring

namespace Erdos320

open Filter

noncomputable def logIndex (n : ℕ) : ℕ := Nat.floor (Real.log (n : ℝ))

theorem log_nat_tendsto : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem loglog_nat_tendsto :
    Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto

theorem logloglog_nat_tendsto :
    Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
  Real.tendsto_log_atTop.comp loglog_nat_tendsto

theorem eventually_log_scale_conditions :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 2 ≤ logIndex n ∧
      (logIndex n : ℝ) ≤ Real.log (n : ℝ) ∧ logIndex n < n ∧
      Real.exp 3 < Real.log (Real.log (n : ℝ)) ∧
      2 ≤ Real.log (Real.log (Real.log (n : ℝ))) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    log_nat_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_gt_atTop (Real.exp 3)),
    logloglog_nat_tendsto.eventually (eventually_ge_atTop (2 : ℝ))]
    with n hn hl hl₂ hl₃
  have hindex : 2 ≤ logIndex n := Nat.le_floor hl
  have hcast : (logIndex n : ℝ) ≤ Real.log (n : ℝ) :=
    Nat.floor_le (by linarith)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by linarith)
  have hltR : (logIndex n : ℝ) < n := by linarith
  have hlt : logIndex n < n := by exact_mod_cast hltR
  exact ⟨hn, hindex, hcast, hlt, hl₂, hl₃⟩

theorem eventually_full_product_step :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (Real.log (n : ℝ))) *
          stoppedProduct (logIndex n) (Real.log (Real.log (logIndex n : ℝ))) ≤
        stoppedProduct n (Real.log (Real.log (n : ℝ))) := by
  filter_upwards [eventually_log_scale_conditions] with n hn
  exact log_factor_product_of_le_log hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.2.1

end Erdos320
