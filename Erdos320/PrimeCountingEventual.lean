import Erdos320.PrimeCounting
import Erdos320.LowerCofactors
import Erdos320.LowerCutoffGrowth

namespace Erdos320

open Filter

theorem eventually_basic_prime_conditions :
    ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) ≤ N ∧ 8 ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ≤ (N : ℝ) / 4 ∧ Real.log (N : ℝ) ^ 5 ≤ N ∧
      1 ≤ Real.log (Real.log ((N + 1 : ℕ) : ℝ)) ∧
      Real.log (Real.log ((N + 1 : ℕ) : ℝ)) ≤ Real.log (N : ℝ) := by
  have hsmall := Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ) < 1 / 4)
  have hpower := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (s := 1)
    (by norm_num)).def (by norm_num : (0 : ℝ) < 1)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    log_nat_tendsto.eventually (eventually_ge_atTop (8 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    hcast.eventually hsmall, hcast.eventually hpower]
    with N hN hlog hloglog hs hp
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := by linarith
  have hl₀ : 0 < Real.log (N : ℝ) := by linarith
  have hs' : Real.log (N : ℝ) ≤ (1 / 4 : ℝ) * N := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_pos hN₀, abs_of_pos hl₀] using hs
  have hp' : Real.log (N : ℝ) ^ 5 ≤ N := by
    calc
      Real.log (N : ℝ) ^ 5 ≤ |Real.log (N : ℝ) ^ 5| := le_abs_self _
      _ ≤ N := by
        simpa only [Real.rpow_natCast, Real.rpow_ofNat, Real.rpow_one, Real.norm_eq_abs,
          abs_of_pos hN₀, one_mul] using hp
  have harg : Real.log (N : ℝ) ≤ Real.log (((N + 1 : ℕ) : ℝ)) :=
    Real.log_le_log hN₀ (by push_cast; linarith)
  have hz₁ : 1 ≤ Real.log (Real.log (((N + 1 : ℕ) : ℝ))) :=
    hloglog.trans (Real.log_le_log hl₀ harg)
  have hN1₀ : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlN1₀ : 0 < Real.log (((N + 1 : ℕ) : ℝ)) :=
    Real.log_pos (by push_cast; linarith)
  have harg₂ : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by push_cast; linarith
  have hh := Real.log_le_log hN1₀ harg₂
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN₀.ne'] at hh
  have hz := Real.log_le_sub_one_of_pos hlN1₀
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  refine ⟨hNR, hlog, ?_, hp', hz₁, ?_⟩ <;> linarith

theorem eventual_prime_difference_of_cutoff_error
    (hcut : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ Real.sqrt (Real.log N) →
      (compatibilityCutoff m : ℝ) * m * Real.log N ^ 5 ≤ N) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      1 ≤ m → m ≤ lowerCofactorBound N →
      ((1 - 1 / Real.log (Real.log (((N + 1 : ℕ) : ℝ))) ^ 2) *
          ((N : ℝ) + 1) / Real.log N) / m ≤
        (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventual_psi_error_le_log_power 6)
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_basic_prime_conditions, hcut,
    hsqrt.eventually (eventually_ge_atTop B)] with N hN hcutN hBN
  intro m hm hmy
  have hmR : (m : ℝ) ≤ Real.sqrt (Real.log N) :=
    (by exact_mod_cast hmy : (m : ℝ) ≤ lowerCofactorBound N).trans
      (lowerCofactorBound_cast_le N)
  exact uniform_prime_difference_of_bounds hN.1 hN.2.1 hN.2.2.1
    hN.2.2.2.1 hN.2.2.2.2.1 hN.2.2.2.2.2 hcutN
      (fun x hx => hB x (hBN.trans hx)) m hm hmR

theorem eventual_uniform_prime_difference :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      1 ≤ m → m ≤ lowerCofactorBound N →
      ((1 - 1 / Real.log (Real.log (((N + 1 : ℕ) : ℝ))) ^ 2) *
          ((N : ℝ) + 1) / Real.log N) / m ≤
        (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) :=
  eventual_prime_difference_of_cutoff_error eventually_uniform_cutoff_error

end Erdos320
