import Erdos320.LowerAnalytic.Losses
import Erdos320.LogIntegral
import Erdos320.LogProduct
import Mathlib.Analysis.Real.Sqrt

namespace Erdos320.LowerAnalytic

/-- The depth grows with the input. Squaring reserves room for all losses. -/
noncomputable def cutoff (H : ℝ) : ℕ → ℝ
  | 0 => H
  | k + 1 => Real.exp ((cutoff H k) ^ 2)

theorem cutoff_ge_base {H : ℝ} (hH : 1 ≤ H) (k : ℕ) : H ≤ cutoff H k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have ha : 1 ≤ cutoff H k := hH.trans ih
      have hexp := Real.add_one_le_exp ((cutoff H k) ^ 2)
      change H ≤ Real.exp ((cutoff H k) ^ 2)
      nlinarith

theorem cutoff_pos {H : ℝ} (hH : 1 ≤ H) (k : ℕ) : 0 < cutoff H k :=
  lt_of_lt_of_le (by linarith) (cutoff_ge_base hH k)

theorem cutoff_add_index_le {H : ℝ} (hH : 1 ≤ H) (k : ℕ) :
    H + k ≤ cutoff H k := by
  induction k with
  | zero => simp [cutoff]
  | succ k ih =>
      have ha : 1 ≤ cutoff H k := hH.trans (cutoff_ge_base hH k)
      have hexp := Real.add_one_le_exp ((cutoff H k) ^ 2)
      change H + (k + 1 : ℕ) ≤ Real.exp ((cutoff H k) ^ 2)
      push_cast
      nlinarith

theorem cutoff_step_log_growth {H : ℝ} (hH : 16 ≤ H) (k : ℕ) :
    16 * Real.log (cutoff H k) ≤ Real.log (cutoff H (k + 1)) := by
  have hH1 : 1 ≤ H := by linarith
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
  have hlog := Real.log_le_sub_one_of_pos (cutoff_pos hH1 k)
  simp only [cutoff, Real.log_exp]
  nlinarith

/-- The geometric epsilon is tiny, but the threshold grows faster. -/
theorem epsilon_sq_log_cutoff_ge_one {H : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (k : ℕ) :
    1 ≤ epsilon k ^ 2 * Real.log (cutoff H k) := by
  induction k with
  | zero => norm_num [epsilon, cutoff]; nlinarith
  | succ k ih =>
      have hgrowth := cutoff_step_log_growth hH k
      have hmul := mul_le_mul_of_nonneg_left hgrowth (sq_nonneg (epsilon (k + 1)))
      calc
        1 ≤ epsilon k ^ 2 * Real.log (cutoff H k) := ih
        _ = epsilon (k + 1) ^ 2 * (16 * Real.log (cutoff H k)) := by
          rw [epsilon_succ]
          ring
        _ ≤ _ := hmul

theorem iterLog_shift (k : ℕ) (x : ℝ) :
    iterLog (k + 1) x = iterLog k (Real.log x) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterLog] using congrArg Real.log ih

/-- Every retained ordinary logarithm stays in a positive fixed range. -/
theorem iterLog_ge_base_of_cutoff {H : ℝ} (hH : 1 ≤ H) (k : ℕ) :
    ∀ x : ℝ, cutoff H k ≤ x → ∀ j : ℕ, j ≤ k → H ≤ iterLog j x := by
  induction k with
  | zero =>
      intro x hx j hj
      have hj0 : j = 0 := by omega
      simpa [hj0, iterLog, cutoff] using hx
  | succ k ih =>
      intro x hx j hj
      cases j with
      | zero =>
          exact (cutoff_ge_base hH (k + 1)).trans hx
      | succ j =>
          have hapos := cutoff_pos hH k
          have hlog : cutoff H k ≤ Real.log x := by
            have h := Real.log_le_log (Real.exp_pos ((cutoff H k) ^ 2)) hx
            have ha : 1 ≤ cutoff H k := hH.trans (cutoff_ge_base hH k)
            simp only [Real.log_exp] at h
            nlinarith
          rw [iterLog_shift]
          exact ih (Real.log x) hlog j (by omega)

theorem cutoff_le_power {H L : ℝ} (hH : 16 ≤ H) (k : ℕ)
    (hL : cutoff H k ^ 2 ≤ L) :
    cutoff H k ≤ L ^ (1 - epsilon k) := by
  have hH1 : 1 ≤ H := by linarith
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
  have hL1 : 1 ≤ L := by nlinarith
  have hroot : cutoff H k ≤ Real.sqrt L :=
    (Real.le_sqrt (by linarith : 0 ≤ cutoff H k) (by linarith : 0 ≤ L)).mpr hL
  have he := epsilon_le k
  calc
    cutoff H k ≤ Real.sqrt L := hroot
    _ = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
    _ ≤ L ^ (1 - epsilon k) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

theorem power_le_epsilon_mul {H L : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (k : ℕ) (hL : cutoff H k ≤ L) :
    L ^ (1 - epsilon k) ≤ epsilon k * L := by
  have hH1 : 1 ≤ H := by linarith
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
  have hLpos : 0 < L := lt_of_lt_of_le (cutoff_pos hH1 k) hL
  have he := epsilon_pos k
  have hsquare := epsilon_sq_log_cutoff_ge_one hH hlogH k
  have hlog : Real.log (cutoff H k) ≤ Real.log L :=
    Real.log_le_log (cutoff_pos hH1 k) hL
  have hsquareL : 1 ≤ epsilon k ^ 2 * Real.log L :=
    hsquare.trans (mul_le_mul_of_nonneg_left hlog (sq_nonneg _))
  have hinv : 1 / epsilon k ≤ epsilon k * Real.log L := by
    apply (div_le_iff₀ he).mpr
    nlinarith
  have hsmallLog := Real.one_sub_inv_le_log_of_pos he
  have hexponent : Real.log L * (1 - epsilon k) ≤
      Real.log (epsilon k) + Real.log L := by
    rw [inv_eq_one_div] at hsmallLog
    nlinarith
  rw [Real.rpow_def_of_pos hLpos]
  calc
    Real.exp (Real.log L * (1 - epsilon k)) ≤
        Real.exp (Real.log (epsilon k) + Real.log L) := Real.exp_le_exp.mpr hexponent
    _ = epsilon k * L := by rw [Real.exp_add, Real.exp_log he, Real.exp_log hLpos]

theorem two_le_epsilon_mul {H L : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (k : ℕ) (hL : cutoff H k ≤ L) :
    2 ≤ epsilon k * L := by
  have hH1 : 1 ≤ H := by linarith
  have hapos := cutoff_pos hH1 k
  have hA := epsilon_sq_log_cutoff_ge_one hH hlogH k
  have hlog := Real.log_le_sub_one_of_pos hapos
  have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg (epsilon k))
  have he := epsilon_le k
  have he0 := (epsilon_pos k).le
  have ha0 := hapos.le
  have hprod : 0 ≤ epsilon k * cutoff H k := mul_nonneg he0 ha0
  have hsmall := mul_nonneg (show 0 ≤ 1 / 2 - epsilon k by linarith) hprod
  have hbase : 2 ≤ epsilon k * cutoff H k := by nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_left hL he0)

end Erdos320.LowerAnalytic
