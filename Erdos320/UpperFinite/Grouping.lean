import Erdos320.UpperRecurrence
import Erdos320.LogScale
import Mathlib.Data.Nat.Cast.Order.Field

namespace Erdos320

/-- The prime divisors contributing to the quotient `m`. -/
noncomputable def quotientPrimeFiber (N m : ℕ) : Finset ℕ := by
  classical
  exact (largePrimes N).filter (fun p => N / p = m)

theorem largePrime_quotient_lt_log {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ largePrimes N) : ((N / p : ℕ) : ℝ) < Real.log (N : ℝ) := by
  have hpdata := (Finset.mem_filter.mp hp).2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpdata.1.pos
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmul := (div_lt_iff₀ hlog).mp hpdata.2
  have hdiv : (N : ℝ) / p < Real.log N := by
    apply (div_lt_iff₀ hpR).mpr
    nlinarith
  exact lt_of_le_of_lt Nat.cast_div_le hdiv

theorem largePrime_quotient_mem_logIndex {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ largePrimes N) : N / p ∈ Finset.Icc 1 (logIndex N) := by
  have hppos := (Finset.mem_filter.mp hp).2.1.pos
  have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  apply Finset.mem_Icc.mpr
  exact ⟨(Nat.le_div_iff_mul_le hppos).mpr (by simpa),
    Nat.le_floor (largePrime_quotient_lt_log hN hp).le⟩

/-- Exact grouping, before any analytic estimate or positivity assumption. -/
theorem prime_sum_grouped (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    (∑ p ∈ largePrimes N, f (N / p)) =
      ∑ m ∈ Finset.Icc 1 (logIndex N), (quotientPrimeFiber N m).card * f m := by
  classical
  have hmap : ∀ p ∈ largePrimes N, N / p ∈ Finset.Icc 1 (logIndex N) :=
    fun _ hp => largePrime_quotient_mem_logIndex hN hp
  have h := Finset.sum_fiberwise_of_maps_to' hmap f
  simpa only [Finset.sum_const, nsmul_eq_mul, quotientPrimeFiber] using h.symm

theorem quotientPrimeFiber_interval {N m : ℕ} (hm : 0 < m) :
    ∀ p ∈ quotientPrimeFiber N m,
      Nat.Prime p ∧ (N : ℝ) / (m + 1) < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) / m := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpP, hquot⟩
  have hprime := (Finset.mem_filter.mp hpP).2.1
  have hlowNat : N < p * (m + 1) := by
    simpa [hquot] using Nat.lt_mul_div_succ N hprime.pos
  have hhighNat : m * p ≤ N := by
    simpa [hquot] using Nat.div_mul_le_self N p
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨hprime, (div_lt_iff₀ (show (0 : ℝ) < m + 1 by positivity)).mpr ?_,
    (le_div_iff₀ hmR).mpr ?_⟩
  · exact_mod_cast hlowNat
  · exact_mod_cast (show p * m ≤ N by simpa [Nat.mul_comm] using hhighNat)

end Erdos320
