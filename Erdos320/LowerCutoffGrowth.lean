import Erdos320.LowerCofactors
import Erdos320.LowerCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Original uniform growth estimates for the factorial compatibility cutoff.
The inequality m! ≤ m^m ≤ 2^(m²) is sufficient in the square-root logarithmic
cofactor range; no precise factorial asymptotic is needed.
-/

namespace Erdos320

open Filter

theorem log_two_lt_one : Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at h
  exact h

theorem two_pow_square_le_rpow {N m : ℕ} (hN : 2 ≤ N)
    (hm : (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ))) :
    (2 : ℝ) ^ (m * m) ≤ (N : ℝ) ^ Real.log (2 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsq : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) :=
    (Real.le_sqrt (by positivity) hL).mp hm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hexp : Real.exp (Real.log (2 : ℝ)) = 2 := Real.exp_log (by norm_num)
  calc
    (2 : ℝ) ^ (m * m) =
        Real.exp ((m : ℝ) ^ 2 * Real.log (2 : ℝ)) := by
      rw [← hexp, ← Real.exp_nat_mul]
      congr 1
      norm_num only [Nat.cast_mul, pow_two, Real.log_exp]
    _ ≤ Real.exp (Real.log (N : ℝ) * Real.log (2 : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsq hlog2)
    _ = (N : ℝ) ^ Real.log (2 : ℝ) :=
      (Real.rpow_def_of_pos hNR _).symm

theorem cutoff_cast_le_rpow {N m : ℕ} (hN : 2 ≤ N)
    (hm : (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ))) :
    (compatibilityCutoff m : ℝ) ≤
      2 * (m : ℝ) * (N : ℝ) ^ Real.log (2 : ℝ) := by
  have hnat : (compatibilityCutoff m : ℝ) ≤ 2 * (m : ℝ) * (2 : ℝ) ^ (m * m) := by
    exact_mod_cast compatibilityCutoff_le_two_pow_square m
  exact hnat.trans (mul_le_mul_of_nonneg_left (two_pow_square_le_rpow hN hm) (by positivity))

/-- The discarded small-prime count is uniformly negligible throughout the
square-root logarithmic cofactor range. -/
theorem eventually_uniform_cutoff_error :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) →
      (compatibilityCutoff m : ℝ) * m * Real.log (N : ℝ) ^ 5 ≤ (N : ℝ) := by
  have hs : 0 < 1 - Real.log (2 : ℝ) := sub_pos.mpr log_two_lt_one
  have hsmall := (isLittleO_log_rpow_rpow_atTop (6 : ℝ) hs).def
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  intro m hm1 hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsq : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) :=
    (Real.le_sqrt (by positivity) hL).mp hm
  have hcut := cutoff_cast_le_rpow hN hm
  have hsmall' : Real.log (N : ℝ) ^ 6 ≤
      (1 / 2 : ℝ) * (N : ℝ) ^ (1 - Real.log (2 : ℝ)) := by
    simpa only [Real.norm_eq_abs, Real.rpow_natCast, Real.rpow_ofNat,
      abs_of_nonneg (pow_nonneg hL 6),
      abs_of_nonneg (Real.rpow_nonneg hNpos.le _)] using hsmallN
  have hsmall2 : 2 * Real.log (N : ℝ) ^ 6 ≤
      (N : ℝ) ^ (1 - Real.log (2 : ℝ)) := by linarith
  have hR : 0 ≤ (N : ℝ) ^ Real.log (2 : ℝ) := Real.rpow_nonneg hNpos.le _
  have hL5 : 0 ≤ Real.log (N : ℝ) ^ 5 := pow_nonneg hL 5
  calc
    (compatibilityCutoff m : ℝ) * m * Real.log (N : ℝ) ^ 5 ≤
        (2 * (m : ℝ) * (N : ℝ) ^ Real.log (2 : ℝ)) * m *
          Real.log (N : ℝ) ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcut (by positivity)) hL5
    _ = (2 * (m : ℝ) ^ 2 * Real.log (N : ℝ) ^ 5) *
        (N : ℝ) ^ Real.log (2 : ℝ) := by ring
    _ ≤ (2 * Real.log (N : ℝ) ^ 6) * (N : ℝ) ^ Real.log (2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hR
      nlinarith [mul_le_mul_of_nonneg_right hsq hL5]
    _ ≤ (N : ℝ) ^ (1 - Real.log (2 : ℝ)) *
        (N : ℝ) ^ Real.log (2 : ℝ) := mul_le_mul_of_nonneg_right hsmall2 hR
    _ = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      simp

end Erdos320
