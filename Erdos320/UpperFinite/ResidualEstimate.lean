import Erdos320.UpperFinite.SmoothDenominator
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

namespace Erdos320

private theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound : Real.log x ≤ 2 * Real.sqrt x := by
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hlog
  have hsquare := pow_le_pow_left₀ hlog0 hbound 2
  nlinarith [Real.sq_sqrt hx0]

private theorem sqrt_mul_log_sq_le {x : ℝ} (hx : 1 < x) :
    Real.sqrt x * (Real.log x) ^ 2 ≤ 216 * x / Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hlog := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 6)
  have hcubed := pow_le_pow_left₀ hl.le hlog 3
  have hcubeeq : (x ^ (1 / 6 : ℝ) / (1 / 6 : ℝ)) ^ 3 =
      216 * Real.sqrt x := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num [Real.sqrt_eq_rpow, div_eq_mul_inv]
    ring
  rw [hcubeeq] at hcubed
  apply (le_div_iff₀ hl).mpr
  calc
    (Real.sqrt x * Real.log x ^ 2) * Real.log x =
        Real.sqrt x * Real.log x ^ 3 := by ring
    _ ≤ Real.sqrt x * (216 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hcubed (Real.sqrt_nonneg x)
    _ = 216 * x := by nlinarith [Real.sq_sqrt hx0]

private theorem log_succ_le_eight_quotient (N : ℕ) (hN : 2 ≤ N) :
    Real.log (N + 1 : ℕ) ≤ 8 * ((N : ℝ) / Real.log N) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hNN : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hNN
  rw [Real.log_pow] at hlog
  have htwo : 2 * Real.log (N : ℝ) ≤ 8 * ((N : ℝ) / Real.log N) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hl).mpr
    have hsq := log_sq_le_four_mul (show (1 : ℝ) ≤ N by linarith)
    nlinarith
  exact hlog.trans htwo

theorem log_smoothDenominator_bound (N : ℕ) (hN : 2 ≤ N) :
    Real.log (smoothDenominator N ⌊(N : ℝ) / Real.log N⌋₊ : ℝ) ≤
      (Real.log 4 + 216 / Real.log 2) * ((N : ℝ) / Real.log N) := by
  let q : ℕ := ⌊(N : ℝ) / Real.log N⌋₊
  let r : ℕ := Nat.sqrt N
  let k : ℕ := Nat.log 2 N
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hq : (q : ℝ) ≤ (N : ℝ) / Real.log N :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hl.le)
  have hprimlog : Real.log (primorial q : ℝ) ≤
      Real.log 4 * ((N : ℝ) / Real.log N) := by
    have hpow : (primorial q : ℝ) ≤ (4 : ℝ) ^ q := by
      exact_mod_cast primorial_le_four_pow q
    have hp := Real.log_le_log (show (0 : ℝ) < primorial q by
      exact_mod_cast primorial_pos q) hpow
    rw [Real.log_pow] at hp
    exact hp.trans (by nlinarith)
  have hk : (k : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa [k, Real.logb] using Real.natLog_le_logb N 2
  have hfact : Real.log (r.factorial : ℝ) ≤ (r : ℝ) * Real.log N := by
    have hf : r.factorial ≤ N ^ r :=
      (Nat.factorial_le_pow r).trans (by
        apply Nat.pow_le_pow_left
        exact Nat.sqrt_le_self N)
    have hfR : (r.factorial : ℝ) ≤ (N : ℝ) ^ r := by exact_mod_cast hf
    have hfLog := Real.log_le_log (show (0 : ℝ) < r.factorial by
      exact_mod_cast Nat.factorial_pos r) hfR
    simpa only [Real.log_pow] using hfLog
  have hsmall : (k : ℝ) * Real.log (r.factorial : ℝ) ≤
      (216 / Real.log 2) * ((N : ℝ) / Real.log N) := by
    calc
      (k : ℝ) * Real.log (r.factorial : ℝ) ≤
          (Real.log N / Real.log 2) * ((r : ℝ) * Real.log N) :=
        mul_le_mul hk hfact (Real.log_natCast_nonneg _) (div_nonneg hl.le hl2.le)
      _ ≤ (Real.log N / Real.log 2) * (Real.sqrt N * Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hl.le hl2.le)
        exact mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt hl.le
      _ = (Real.sqrt N * Real.log N ^ 2) / Real.log 2 := by ring
      _ ≤ (216 * (N : ℝ) / Real.log N) / Real.log 2 :=
        div_le_div_of_nonneg_right (sqrt_mul_log_sq_le (show (1 : ℝ) < N by linarith)) hl2.le
      _ = (216 / Real.log 2) * ((N : ℝ) / Real.log N) := by ring
  have hprim0 : (primorial q : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos q).ne'
  have hfact0 : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  change Real.log ((primorial q * r.factorial ^ k : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hprim0 (pow_ne_zero _ hfact0), Real.log_pow]
  nlinarith

theorem residual_log_bound (N : ℕ) (hN : 2 ≤ N) :
    Real.log ((sumsOf (residualBlock N (largePrimes N))).card : ℝ) ≤
      (Real.log 4 + 216 / Real.log 2 + 8) * ((N : ℝ) / Real.log N) := by
  let Z := residualBlock N (largePrimes N)
  have hZpos : ∀ n ∈ Z, 0 < n := by
    intro n hn
    exact lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1
  have hdiv : ∀ n ∈ Z, n ∣ smoothDenominator N ⌊(N : ℝ) / Real.log N⌋₊ := by
    intro n hn
    exact residualBlock_dvd_smoothDenominator N hn
  have hgrid := log_card_sumsOf_le_log_common_denominator Z _
    (smoothDenominator_pos _ _) hZpos hdiv
  have hZcard : Z.card ≤ N := by
    have h := Finset.card_le_card (Finset.sdiff_subset : Z ⊆ Finset.Icc 1 N)
    simpa [Z, residualBlock] using h
  have hZlog : Real.log (Z.card + 1 : ℕ) ≤ 8 * ((N : ℝ) / Real.log N) := by
    have hcast : ((Z.card + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hZcard 1
    exact (Real.log_le_log (by positivity) hcast).trans (log_succ_le_eight_quotient N hN)
  have hdenom := log_smoothDenominator_bound N hN
  dsimp [Z] at hgrid hZlog
  nlinarith

end Erdos320
