import Erdos320.UpperAnalyticApplication
import Erdos320.UpperAnalyticPrimeBlocks

/-!
Original closure of the upper bound. All prime-number-theorem inputs are proved
through the pinned upstream `MediumPNT`, and the exact finite decomposition is
proved in this project. The tail starts at four, preserving a positive kernel
reserve and hence coefficient one through the complete logarithmic iteration.
-/

namespace Erdos320

theorem logS_nonneg (N : ℕ) : 0 ≤ logS N := by
  have hS : 0 < S N := card_sumsOf_pos (Finset.Icc 1 N)
  have hS₁ : 1 ≤ S N := by omega
  exact Real.log_nonneg (by exact_mod_cast hS₁)

noncomputable def initialEntropyKernelMass : ℝ :=
  ∑ m ∈ Finset.Icc 1 3, logS m / ((m : ℝ) * (m + 1))

theorem initialEntropyKernelMass_nonneg : 0 ≤ initialEntropyKernelMass := by
  apply Finset.sum_nonneg
  intro m hm
  exact div_nonneg (logS_nonneg m) (by positivity)

theorem entropy_kernel_sum_split (q : ℕ) (hq : 3 ≤ q) :
    (∑ m ∈ Finset.Icc 1 q, logS m / ((m : ℝ) * (m + 1))) =
      initialEntropyKernelMass +
        ∑ m ∈ Finset.Icc 4 q, logS m / ((m : ℝ) * (m + 1)) := by
  have hunion : Finset.Icc 1 q = Finset.Icc 1 3 ∪ Finset.Icc 4 q := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 1 3) (Finset.Icc 4 q) := by
    apply Finset.disjoint_left.mpr
    intro m hm₁ hm₂
    simp only [Finset.mem_Icc] at hm₁ hm₂
    omega
  rw [hunion, Finset.sum_union hdis]
  rfl

theorem tail_entropy_kernel_bound (q : ℕ) (hq : 3 ≤ q) :
    (∑ m ∈ Finset.Icc 4 q, logS m / ((m : ℝ) * (m + 1))) ≤
      runningMaximum normalizedEntropy q *
        (Real.log (Real.log q) - Real.log (Real.log 3)) := by
  have hterm : ∀ m ∈ Finset.Icc 4 q,
      logS m / ((m : ℝ) * (m + 1)) ≤
        (1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) *
          runningMaximum normalizedEntropy q := by
    intro m hm
    have hm₄ := (Finset.mem_Icc.mp hm).1
    have hm₁ : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    have hm₀ : (0 : ℝ) < m := by linarith
    have hl : 0 < Real.log (m : ℝ) := Real.log_pos hm₁
    have hkernel : 0 ≤ 1 / ((m : ℝ) + 1) / Real.log (m : ℝ) := by positivity
    have hnorm : normalizedEntropy m ≤ runningMaximum normalizedEntropy q :=
      le_runningMaximum_of_le normalizedEntropy (Finset.mem_Icc.mp hm).2
    calc
      logS m / ((m : ℝ) * (m + 1)) =
          (1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) * normalizedEntropy m := by
        dsimp [normalizedEntropy]
        field_simp [hm₀.ne', hl.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hkernel
  calc
    _ ≤ ∑ m ∈ Finset.Icc 4 q,
        (1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) *
          runningMaximum normalizedEntropy q := Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.Icc 4 q, 1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) *
        runningMaximum normalizedEntropy q := (Finset.sum_mul ..).symm
    _ ≤ (Real.log (Real.log q) - Real.log (Real.log 3)) *
        runningMaximum normalizedEntropy q :=
      mul_le_mul_of_nonneg_right (sum_renewalKernel_le q hq)
        (runningMaximum_nonneg normalizedEntropy q)
    _ = _ := by ring

theorem eventual_normalized_upper_recurrence :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
      normalizedEntropy N ≤ A + Real.log (Real.log (Real.log (N : ℝ))) *
        runningMaximum normalizedEntropy (logIndex N) := by
  obtain ⟨A, hA, hrec⟩ := eventual_upper_recurrence
  refine ⟨A + 2 * initialEntropyKernelMass, by nlinarith [initialEntropyKernelMass_nonneg], ?_⟩
  filter_upwards [hrec, eventual_quotientPrimeFiber_bound, eventually_log_scale_conditions,
    eventually_logIndex_three, eventually_renewalError_nonneg, eventually_renewalError_le_one,
    eventually_renewalError_kernel_absorbed] with N hrecN hfiber hN hq₃ hδ₀ hδ₁ habsorb
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN₀ : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN₁
  have hnormalizer : 0 ≤ Real.log (N : ℝ) / (N : ℝ) := div_nonneg hlog.le hN₀.le
  have hδ : 0 ≤ 1 + renewalError N := by linarith
  have hAidentity : (Real.log (N : ℝ) / (N : ℝ)) *
      (A * ((N : ℝ) / Real.log N)) = A := by
    field_simp
  have hnormalized : normalizedEntropy N ≤ A +
      ∑ m ∈ Finset.Icc 1 (logIndex N),
        ((Real.log (N : ℝ) / (N : ℝ)) * (quotientPrimeFiber N m).card) * logS m := by
    calc
      normalizedEntropy N ≤ (Real.log (N : ℝ) / (N : ℝ)) *
          (A * ((N : ℝ) / Real.log N) + ∑ p ∈ largePrimes N, logS (N / p)) :=
        mul_le_mul_of_nonneg_left hrecN hnormalizer
      _ = _ := by
        rw [prime_sum_grouped N hN.1 logS, mul_add, Finset.mul_sum, hAidentity]
        simp only [mul_assoc]
  have hcount : normalizedEntropy N ≤ A + (1 + renewalError N) *
      ∑ m ∈ Finset.Icc 1 (logIndex N), logS m / ((m : ℝ) * (m + 1)) := by
    calc
      _ ≤ A + ∑ m ∈ Finset.Icc 1 (logIndex N),
          ((Real.log (N : ℝ) / (N : ℝ)) * (quotientPrimeFiber N m).card) * logS m :=
        hnormalized
      _ ≤ A + ∑ m ∈ Finset.Icc 1 (logIndex N),
          ((1 + renewalError N) / ((m : ℝ) * (m + 1))) * logS m := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hfiber m hm) (logS_nonneg m)
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _hm
        ring
  rw [entropy_kernel_sum_split (logIndex N) hq₃] at hcount
  have hq₁ : (1 : ℝ) < logIndex N := by exact_mod_cast (by omega : 1 < logIndex N)
  have hq₀ : (0 : ℝ) < logIndex N := by linarith
  have hlogq : Real.log (logIndex N : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log hq₀ hN.2.2.1
  have hloglogq : Real.log (Real.log (logIndex N : ℝ)) ≤
      Real.log (Real.log (Real.log (N : ℝ))) :=
    Real.log_le_log (Real.log_pos hq₁) hlogq
  have hfactor : (1 + renewalError N) *
      (Real.log (Real.log (logIndex N : ℝ)) - Real.log (Real.log 3)) ≤
        Real.log (Real.log (Real.log (N : ℝ))) :=
    (mul_le_mul_of_nonneg_left
      (sub_le_sub_right hloglogq (Real.log (Real.log 3))) hδ).trans habsorb
  have htail : (1 + renewalError N) *
      (∑ m ∈ Finset.Icc 4 (logIndex N), logS m / ((m : ℝ) * (m + 1))) ≤
        runningMaximum normalizedEntropy (logIndex N) *
          Real.log (Real.log (Real.log (N : ℝ))) := by
    calc
      _ ≤ (1 + renewalError N) *
          (runningMaximum normalizedEntropy (logIndex N) *
            (Real.log (Real.log (logIndex N : ℝ)) - Real.log (Real.log 3))) :=
        mul_le_mul_of_nonneg_left (tail_entropy_kernel_bound (logIndex N) hq₃) hδ
      _ = runningMaximum normalizedEntropy (logIndex N) *
          ((1 + renewalError N) *
            (Real.log (Real.log (logIndex N : ℝ)) - Real.log (Real.log 3))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfactor
        (runningMaximum_nonneg normalizedEntropy (logIndex N))
  have hbase : (1 + renewalError N) * initialEntropyKernelMass ≤
      2 * initialEntropyKernelMass :=
    mul_le_mul_of_nonneg_right (by linarith) initialEntropyKernelMass_nonneg
  nlinarith only [hcount, htail, hbase]

/-- The full, unbounded-depth upper estimate for Erdős Problem 320. -/
theorem eventual_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop, logS N ≤ C * scale N := by
  obtain ⟨A, hA, hrec⟩ := eventual_normalized_upper_recurrence
  exact eventual_upper_bound_of_normalized_recurrence A hA.le hrec

end Erdos320
