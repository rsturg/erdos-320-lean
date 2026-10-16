import Erdos320.LogScale
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
The cofactor range for the original lower construction is the square root of
`log N`. These elementary rounding estimates are independent of prime counting.
-/

namespace Erdos320

open Filter

noncomputable def lowerCofactorBound (N : ℕ) : ℕ :=
  ⌊Real.sqrt (Real.log (N : ℝ))⌋₊

theorem lowerCofactorBound_cast_le (N : ℕ) :
    (lowerCofactorBound N : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) :=
  Nat.floor_le (Real.sqrt_nonneg _)

theorem cofactor_sq_le_log {N m : ℕ} (hN : 1 ≤ N)
    (hm : m ≤ lowerCofactorBound N) : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hmR : (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    le_trans (by exact_mod_cast hm) (lowerCofactorBound_cast_le N)
  have hs := Real.sq_sqrt hlog
  nlinarith [Real.sqrt_nonneg (Real.log (N : ℝ)), Nat.cast_nonneg (α := ℝ) m]

theorem lowerCofactorBound_lt {N : ℕ} (hN : 2 ≤ N) : lowerCofactorBound N < N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hloglt : Real.log (N : ℝ) < (N : ℝ) ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    nlinarith
  have hsqrt : Real.sqrt (Real.log (N : ℝ)) < (N : ℝ) :=
    (Real.sqrt_lt hlog (by positivity)).mpr hloglt
  have hcast := lt_of_le_of_lt (lowerCofactorBound_cast_le N) hsqrt
  exact_mod_cast hcast

theorem lowerCofactorBound_ge_three {N : ℕ} (hlog : 9 ≤ Real.log (N : ℝ)) :
    3 ≤ lowerCofactorBound N := by
  apply Nat.le_floor
  apply Real.le_sqrt_of_sq_le
  norm_num
  exact hlog

theorem half_sqrt_le_lowerCofactorBound {N : ℕ}
    (hlog : 4 ≤ Real.log (N : ℝ)) :
    Real.sqrt (Real.log (N : ℝ)) / 2 ≤ (lowerCofactorBound N : ℝ) := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.le_sqrt_of_sq_le (by norm_num; exact hlog)
  have hfloor := Nat.lt_floor_add_one (Real.sqrt (Real.log (N : ℝ)))
  change Real.sqrt (Real.log (N : ℝ)) < (lowerCofactorBound N : ℝ) + 1 at hfloor
  linarith

theorem lower_cofactor_log_endpoint {N : ℕ} (hN : 3 ≤ N)
    (hlog : 9 ≤ Real.log (N : ℝ))
    (hloglog : 10 ≤ Real.log (Real.log (N : ℝ))) :
    Real.log (Real.log (Real.log ((N + 1 : ℕ) : ℝ))) - 2 ≤
      Real.log (Real.log (lowerCofactorBound N : ℝ)) := by
  let z : ℝ := Real.log (Real.log (N : ℝ))
  let z' : ℝ := Real.log (Real.log ((N + 1 : ℕ) : ℝ))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hspos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hLpos
  have hyhalf := half_sqrt_le_lowerCofactorBound (by linarith : 4 ≤ Real.log (N : ℝ))
  have hlogy : z / 2 - Real.log 2 ≤ Real.log (lowerCofactorBound N : ℝ) := by
    have h := Real.log_le_log (div_pos hspos (by norm_num)) hyhalf
    rw [Real.log_div hspos.ne' (by norm_num), Real.log_sqrt hLpos.le] at h
    exact h
  have hNnextsq : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hLnext : Real.log ((N + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hNnextsq
    simpa [Real.log_pow] using h
  have hLnextpos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have hzz : z' ≤ Real.log 2 + z := by
    have h := Real.log_le_log hLnextpos hLnext
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLpos.ne'] at h
  have hmono : z ≤ z' := by
    apply Real.log_le_log hLpos
    apply Real.log_le_log hNpos
    exact_mod_cast (Nat.le_succ N)
  have hzpos : 0 < z' := by
    change 10 ≤ z at hloglog
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hquarter : z' / 4 ≤ Real.log (lowerCofactorBound N : ℝ) := by
    change 10 ≤ z at hloglog
    linarith
  have houter := Real.log_le_log (div_pos hzpos (by norm_num)) hquarter
  rw [Real.log_div hzpos.ne' (by norm_num : (4 : ℝ) ≠ 0)] at houter
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  change Real.log z' - 2 ≤ _
  linarith

theorem eventually_lower_cofactor_conditions :
    ∀ᶠ N : ℕ in atTop,
      3 ≤ lowerCofactorBound N ∧ lowerCofactorBound N < N ∧
      Real.log (Real.log (Real.log ((N + 1 : ℕ) : ℝ))) - 2 ≤
        Real.log (Real.log (lowerCofactorBound N : ℝ)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    log_nat_tendsto.eventually (eventually_ge_atTop (9 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (10 : ℝ))]
      with N hN hL hz
  exact ⟨lowerCofactorBound_ge_three hL, lowerCofactorBound_lt (by omega),
    lower_cofactor_log_endpoint hN hL hz⟩

end Erdos320
