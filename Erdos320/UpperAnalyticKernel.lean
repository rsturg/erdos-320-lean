import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Original estimates for the logarithmic renewal kernel in Erdős Problem 320.

The finite tail begins at four. Integration begins at three, leaving the
strictly positive reserve `log (log 3)`. This reserve absorbs a vanishing
prime-counting error while retaining coefficient one at every recursion depth.
-/

namespace Erdos320

noncomputable def logarithmicKernel (x : ℝ) : ℝ := 1 / (x * Real.log x)

theorem logarithmicKernel_antitone :
    AntitoneOn logarithmicKernel (Set.Ici (3 : ℝ)) := by
  intro a ha b hb hab
  have ha₀ : 0 < a := by linarith [show (3 : ℝ) ≤ a from ha]
  have hb₀ : 0 < b := ha₀.trans_le hab
  have ha₁ : 1 < a := by linarith [show (3 : ℝ) ≤ a from ha]
  have hla : 0 < Real.log a := Real.log_pos ha₁
  have hl : Real.log a ≤ Real.log b := Real.log_le_log ha₀ hab
  have hp : a * Real.log a ≤ b * Real.log b :=
    mul_le_mul hab hl hla.le hb₀.le
  exact one_div_le_one_div_of_le (mul_pos ha₀ hla) hp

theorem hasDerivAt_loglog {x : ℝ} (hx : 3 ≤ x) :
    HasDerivAt (fun t : ℝ => Real.log (Real.log t)) (logarithmicKernel x) x := by
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx₁
  simpa [logarithmicKernel, div_eq_mul_inv, mul_inv_rev, mul_comm] using
    (Real.hasDerivAt_log hx₀.ne').log hl.ne'

theorem integral_logarithmicKernel {M : ℝ} (hM : 3 ≤ M) :
    (∫ t in (3 : ℝ)..M, logarithmicKernel t) =
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  have ha : AntitoneOn logarithmicKernel (Set.uIcc (3 : ℝ) M) := by
    rw [Set.uIcc_of_le hM]
    exact logarithmicKernel_antitone.mono (fun _ hx => hx.1)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_loglog hx.1
  · exact ha.intervalIntegrable

theorem sum_logarithmicKernel_le_loglog_sub (M : ℕ) (hM : 3 ≤ M) :
    (∑ i ∈ Finset.Ico 3 M, logarithmicKernel (i + 1 : ℕ)) ≤
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  have ha : AntitoneOn logarithmicKernel (Set.Icc (3 : ℝ) M) :=
    logarithmicKernel_antitone.mono (fun _ hx => hx.1)
  calc
    (∑ i ∈ Finset.Ico 3 M, logarithmicKernel (i + 1 : ℕ))
        ≤ ∫ t in (3 : ℝ)..(M : ℝ), logarithmicKernel t :=
      ha.sum_le_integral_Ico hM
    _ = Real.log (Real.log M) - Real.log (Real.log 3) :=
      integral_logarithmicKernel (by exact_mod_cast hM)

/-- The reciprocal-log tail in its shifted-index form. -/
theorem sum_renewalKernel_shifted_le (M : ℕ) (hM : 3 ≤ M) :
    (∑ i ∈ Finset.Ico 3 M,
      1 / (((i + 1 : ℕ) : ℝ) + 1) / Real.log (i + 1 : ℕ)) ≤
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  calc
    _ ≤ ∑ i ∈ Finset.Ico 3 M, logarithmicKernel (i + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi₃ : 3 ≤ i := (Finset.mem_Ico.mp hi).1
      have hi₀ : (0 : ℝ) < (i + 1 : ℕ) := by positivity
      have hi₁ : (1 : ℝ) < (i + 1 : ℕ) := by exact_mod_cast (by omega : 1 < i + 1)
      have hl : 0 < Real.log (i + 1 : ℕ) := Real.log_pos hi₁
      have hden : ((i + 1 : ℕ) : ℝ) * Real.log (i + 1 : ℕ) ≤
          (((i + 1 : ℕ) : ℝ) + 1) * Real.log (i + 1 : ℕ) := by nlinarith
      simpa [logarithmicKernel, div_eq_mul_inv, mul_inv_rev, mul_comm] using
        one_div_le_one_div_of_le (mul_pos hi₀ hl) hden
    _ ≤ Real.log (Real.log M) - Real.log (Real.log 3) :=
      sum_logarithmicKernel_le_loglog_sub M hM

theorem sum_renewalKernel_le (M : ℕ) (hM : 3 ≤ M) :
    (∑ m ∈ Finset.Icc 4 M, 1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) ≤
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  let f : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) / Real.log (m : ℝ)
  have hshift : (∑ m ∈ Finset.Icc 4 M, f m) =
      ∑ i ∈ Finset.Ico 3 M, f (i + 1) := by
    simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.reduceAdd, Nat.add_comm] using
      (Finset.sum_Ico_add f 3 M 1).symm
  change (∑ m ∈ Finset.Icc 4 M, f m) ≤ _
  rw [hshift]
  exact sum_renewalKernel_shifted_le M hM

theorem loglog_three_pos : 0 < Real.log (Real.log (3 : ℝ)) := by
  apply Real.log_pos
  have h := Real.log_lt_log (Real.exp_pos (1 : ℝ)) Real.exp_one_lt_three
  simpa only [Real.log_exp] using h

/-- A positive reserve in the kernel absorbs the error without a repeated
fixed loss in the recurrence coefficient. -/
theorem multiplicative_error_absorbed_by_margin {δ T d : ℝ}
    (hδ : 0 ≤ δ) (hd : 0 < d) (herror : δ * T ≤ d) :
    (1 + δ) * (T - d) ≤ T := by
  have hδd : 0 ≤ δ * d := mul_nonneg hδ hd.le
  nlinarith

theorem eventual_multiplicative_error_absorbed_by_margin
    (δ T : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hδ : ∀ᶠ n in Filter.atTop, 0 ≤ δ n)
    (herror : Filter.Tendsto (fun n => δ n * T n) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, (1 + δ n) * (T n - d) ≤ T n := by
  have hsmall : ∀ᶠ n in Filter.atTop, δ n * T n < d :=
    herror.eventually (gt_mem_nhds hd)
  filter_upwards [hδ, hsmall] with n hn hs
  exact multiplicative_error_absorbed_by_margin hn hd hs.le

/-- A denominator loss `1-z`, with `z ≤ 1/2`, and a relative numerator error
`e` can be bounded with a coefficient tending to one when `z,e → 0`.
This is the arithmetic normalization used for a quantitative prime interval.
-/
theorem denominator_loss_normalization {B H L z e : ℝ}
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hz_half : z ≤ 1 / 2)
    (he : 0 ≤ e) (hbound : B * L * (1 - z) ≤ H * (1 + e)) :
    B * L ≤ H * (1 + 2 * z + 2 * e) := by
  have hz₁ : 0 < 1 - z := by linarith
  have hreserve : 0 ≤ (z + e) * (1 - 2 * z) :=
    mul_nonneg (add_nonneg hz he) (by linarith)
  have hfactor : 1 + e ≤ (1 + 2 * z + 2 * e) * (1 - z) := by
    nlinarith
  have hnormalized : (B * L) * (1 - z) ≤
      (H * (1 + 2 * z + 2 * e)) * (1 - z) := by
    calc
      _ ≤ H * (1 + e) := hbound
      _ ≤ H * ((1 + 2 * z + 2 * e) * (1 - z)) :=
        mul_le_mul_of_nonneg_left hfactor hH
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hz₁).mp hnormalized

end Erdos320
