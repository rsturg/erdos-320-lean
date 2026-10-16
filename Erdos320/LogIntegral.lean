import Erdos320.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Original elementary power-comparison tools for the lower renewal argument. -/

namespace Erdos320

noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iterLog k x)

noncomputable def logFactors (k : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range k, iterLog (j + 1) x

theorem log_lower_near_one {a : ℝ} (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1) :
    -2 * (1 - a) ≤ Real.log a := by
  have ha₀ : 0 < a := by linarith
  have h := Real.one_sub_inv_le_log_of_pos ha₀
  have hi : -2 * (1 - a) ≤ 1 - a⁻¹ := by
    apply (mul_le_mul_iff_of_pos_right ha₀).mp
    have hcancel : a⁻¹ * a = 1 := inv_mul_cancel₀ ha₀.ne'
    nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith)
      (show 0 ≤ 2 * a - 1 by linarith)]
  exact hi.trans h

theorem log_mul_lower_scaled {a u : ℝ}
    (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hu : 0 < u) (hlu : 2 ≤ Real.log u) :
    a * Real.log u ≤ Real.log (a * u) := by
  have ha₀ : 0 < a := by linarith
  rw [Real.log_mul ha₀.ne' hu.ne']
  have haLog := log_lower_near_one ha ha₁
  nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith)
    (show 0 ≤ Real.log u - 2 by linarith)]

theorem iterLog_power_lower {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      a * iterLog j x ≤ iterLog j (x ^ a) := by
  intro j hj hjk
  induction j with
  | zero => omega
  | succ j ih =>
      cases j with
      | zero =>
          simp only [iterLog]
          rw [Real.log_rpow hx]
      | succ j =>
          have hprev : a * iterLog (j + 1) x ≤ iterLog (j + 1) (x ^ a) :=
            ih (by omega) (by omega)
          have hu : 0 < iterLog (j + 1) x :=
            lt_of_lt_of_le (Real.exp_pos 2) (hlogs (j + 1) (by omega) (by omega))
          have ha₀ : 0 < a := by linarith
          have hprod : 0 < a * iterLog (j + 1) x := mul_pos ha₀ hu
          have hnext : 2 ≤ Real.log (iterLog (j + 1) x) := by
            have he : (2 : ℝ) ≤ Real.exp 2 := by
              have := Real.add_one_le_exp (2 : ℝ)
              linarith
            exact he.trans (hlogs (j + 2) (by omega) (by omega))
          calc
            a * iterLog (j + 2) x = a * Real.log (iterLog (j + 1) x) := rfl
            _ ≤ Real.log (a * iterLog (j + 1) x) :=
              log_mul_lower_scaled ha ha₁ hu hnext
            _ ≤ Real.log (iterLog (j + 1) (x ^ a)) := Real.log_le_log hprod hprev
            _ = iterLog (j + 2) (x ^ a) := rfl

theorem logFactors_power_lower {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x) :
    a ^ k * logFactors k x ≤ logFactors k (x ^ a) := by
  have ha₀ : 0 ≤ a := by linarith
  have hnonneg : ∀ j ∈ Finset.range k, 0 ≤ a * iterLog (j + 1) x := by
    intro j hj
    exact mul_nonneg ha₀ (le_trans (le_of_lt (Real.exp_pos 2))
      (hlogs (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)))
  have hp := Finset.prod_le_prod hnonneg (fun j hj =>
    iterLog_power_lower hx ha ha₁ hlogs (j + 1) (by omega)
      (by have := Finset.mem_range.mp hj; omega))
  simpa [logFactors, Finset.prod_mul_distrib] using hp

theorem iterLog_mono_of_positive {k : ℕ} {x y : ℝ}
    (hxy : x ≤ y) (hx : ∀ j : ℕ, j < k → 0 < iterLog j x) :
    iterLog k x ≤ iterLog k y := by
  induction k with
  | zero => exact hxy
  | succ k ih =>
      exact Real.log_le_log (hx k (by omega))
        (ih (fun j hj => hx j (by omega)))

theorem iterLog_power_pos {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x) :
    ∀ j : ℕ, j ≤ k → 0 < iterLog j (x ^ a) := by
  intro j hj
  cases j with
  | zero => exact Real.rpow_pos_of_pos hx _
  | succ j =>
      have ha₀ : 0 < a := by linarith
      have hlarge : 0 < iterLog (j + 1) x :=
        lt_of_lt_of_le (Real.exp_pos 2) (hlogs (j + 1) (by omega) hj)
      exact lt_of_lt_of_le (mul_pos ha₀ hlarge)
        (iterLog_power_lower hx ha ha₁ hlogs (j + 1) (by omega) hj)

theorem logFactors_monotone_above_power {k : ℕ} {x a y : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x)
    (hy : x ^ a ≤ y) :
    logFactors k (x ^ a) ≤ logFactors k y := by
  apply Finset.prod_le_prod
  · intro j hj
    exact (iterLog_power_pos hx ha ha₁ hlogs (j + 1)
      (by have := Finset.mem_range.mp hj; omega)).le
  · intro j hj
    apply iterLog_mono_of_positive hy
    intro i hi
    exact iterLog_power_pos hx ha ha₁ hlogs i
      (by have := Finset.mem_range.mp hj; omega)

theorem iterLog_continuousOn {k : ℕ} {x : ℝ}
    (hx : ∀ j : ℕ, j < k → 0 < iterLog j x) :
    ContinuousOn (iterLog k) (Set.Ici x) := by
  induction k with
  | zero =>
      change ContinuousOn id (Set.Ici x)
      exact continuousOn_id
  | succ k ih =>
      have hsub : ∀ j : ℕ, j < k → 0 < iterLog j x :=
        fun j hj => hx j (by omega)
      apply (ih hsub).log
      intro y hy
      exact ne_of_gt ((hx k (by omega)).trans_le (iterLog_mono_of_positive hy hsub))

theorem logFactors_continuousOn {k : ℕ} {x : ℝ}
    (hx : ∀ j : ℕ, j < k → 0 < iterLog j x) :
    ContinuousOn (logFactors k) (Set.Ici x) := by
  unfold logFactors
  apply continuousOn_finsetProd
  intro j hj
  apply iterLog_continuousOn
  intro i hi
  exact hx i (by have := Finset.mem_range.mp hj; omega)

theorem integral_logFactors_power_lower {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x)
    (horder : x ^ a ≤ x) :
    (x - x ^ a) * a ^ k * logFactors k x ≤
      ∫ w in x ^ a..x, logFactors k w := by
  have hc : ContinuousOn (logFactors k) (Set.Icc (x ^ a) x) :=
    (logFactors_continuousOn (fun j hj =>
      iterLog_power_pos hx ha ha₁ hlogs j (by omega))).mono
        (fun _ hy => hy.1)
  have hi : IntervalIntegrable (logFactors k) MeasureTheory.volume (x ^ a) x :=
    hc.intervalIntegrable_of_Icc horder
  have hpoint : ∀ w ∈ Set.Icc (x ^ a) x,
      a ^ k * logFactors k x ≤ logFactors k w := by
    intro w hw
    exact (logFactors_power_lower hx ha ha₁ hlogs).trans
      (logFactors_monotone_above_power hx ha ha₁ hlogs hw.1)
  have h := intervalIntegral.integral_mono_on horder
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => a ^ k * logFactors k x) MeasureTheory.volume (x ^ a) x)
    hi hpoint
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using h

end Erdos320
