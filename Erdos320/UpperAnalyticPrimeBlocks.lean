import Erdos320.UpperAnalyticUniform
import Erdos320.UpperAnalyticLimits
import Erdos320.UpperAnalyticPNT
import Erdos320.UpperFinite.Grouping

/-! Original uniform quantitative bound for the exact quotient-prime fibers. -/

namespace Erdos320

theorem eventual_quotientPrimeFiber_bound :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ m ∈ Finset.Icc 1 (logIndex N),
      (Real.log (N : ℝ) / (N : ℝ)) * (quotientPrimeFiber N m).card ≤
        (1 + renewalError N) / ((m : ℝ) * (m + 1)) := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (eventual_psi_error_le_log_power 4)
  have hcut : Filter.Tendsto
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ) + 1))
      Filter.atTop Filter.atTop :=
    tendsto_div_log_add_one_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_scale_conditions,
    log_nat_tendsto.eventually eventually_log_add_one_le_half,
    hcut.eventually (Filter.eventually_ge_atTop X₀)] with N hN hL hcutN
  intro m hm
  have hm₁ : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm₁R : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hmL : (m : ℝ) ≤ Real.log (N : ℝ) :=
    (show (m : ℝ) ≤ logIndex N by exact_mod_cast (Finset.mem_Icc.mp hm).2).trans hN.2.2.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLr : 0 < Real.log (N : ℝ) := by linarith [hL.1]
  have hden : (m : ℝ) + 1 ≤ Real.log (N : ℝ) + 1 := by linarith
  have hcut_le_a : (N : ℝ) / (Real.log (N : ℝ) + 1) ≤ (N : ℝ) / ((m : ℝ) + 1) :=
    div_le_div_of_nonneg_left hNr.le hm₁R hden
  have ha₀ : 0 < (N : ℝ) / ((m : ℝ) + 1) := div_pos hNr hm₁R
  have hab : (N : ℝ) / ((m : ℝ) + 1) ≤ (N : ℝ) / m :=
    div_le_div_of_nonneg_left hNr.le hmR (by linarith)
  have hlogₐ : Real.log (N : ℝ) - Real.log (Real.log (N : ℝ) + 1) ≤
      Real.log ((N : ℝ) / ((m : ℝ) + 1)) := by
    rw [Real.log_div hNr.ne' hm₁R.ne']
    have hlogden : Real.log ((m : ℝ) + 1) ≤ Real.log (Real.log (N : ℝ) + 1) :=
      Real.log_le_log hm₁R hden
    linarith
  have hlog_b : Real.log (N : ℝ) / 2 ≤ Real.log ((N : ℝ) / m) := by
    have hlogab := Real.log_le_log ha₀ hab
    linarith [hL.2.2]
  have hₐ := hX₀ ((N : ℝ) / ((m : ℝ) + 1)) (hcutN.trans hcut_le_a)
  have h_b := hX₀ ((N : ℝ) / m) (hcutN.trans (hcut_le_a.trans hab))
  have hbound := prime_interval_normalized_uniform (quotientPrimeFiber N m)
    (N : ℝ) (Real.log (N : ℝ)) (m : ℝ) (Real.log (Real.log (N : ℝ) + 1))
    hNr hL.1 hmR hmL hL.2.1 hL.2.2 hlogₐ hlog_b
    (quotientPrimeFiber_interval hmpos) hₐ h_b
  simpa only [renewalError, renewalLogError] using hbound

end Erdos320
