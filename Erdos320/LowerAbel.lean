import Erdos320.LowerCounting

/-!
An exact discrete partial-summation identity for the independent-denominator
count, followed by the finite renewal inequality. Analytic estimates for the
prime counts enter through one explicit, separately proved hypothesis.
-/

namespace Erdos320

noncomputable def independentCount (N : ℕ) : ℝ :=
  (independentDenominators N).card

noncomputable def independentWeight (N : ℕ) : ℝ :=
  ∑ d ∈ independentDenominators N, 1 / (d : ℝ)

theorem independentCount_nonneg (N : ℕ) : 0 ≤ independentCount N := by
  unfold independentCount
  positivity

theorem primeCounting_le_independentCount (N : ℕ) :
    (Nat.primeCounting N : ℝ) ≤ independentCount N := by
  unfold independentCount
  exact_mod_cast primeCounting_le_independent_card N

theorem independentCount_log_lower (N : ℕ) :
    independentCount N * Real.log 2 ≤ logS N :=
  independent_count_log_lower N

theorem independentCount_succ (N : ℕ) :
    independentCount (N + 1) = independentCount N +
      if IndependentDenominator (N + 1) then 1 else 0 := by
  have hnew : N + 1 ∉ independentDenominators N := by
    simp [independentDenominators]
  unfold independentCount
  rw [independentDenominators_succ]
  split_ifs <;> simp [hnew]

theorem independentWeight_succ (N : ℕ) :
    independentWeight (N + 1) = independentWeight N +
      if IndependentDenominator (N + 1) then 1 / ((N + 1 : ℕ) : ℝ) else 0 := by
  classical
  have hnew : N + 1 ∉ independentDenominators N := by
    simp [independentDenominators]
  unfold independentWeight
  rw [independentDenominators_succ]
  split_ifs <;> simp [hnew, add_comm]

/-- Finite Abel summation, with no discarded endpoints or analytic limits. -/
theorem independent_weight_abel (N : ℕ) :
    independentWeight N = independentCount N / (N + 1) +
      ∑ m ∈ Finset.Icc 1 N,
        independentCount m / ((m : ℝ) * (m + 1)) := by
  induction N with
  | zero => simp [independentWeight, independentCount, independentDenominators]
  | succ N ih =>
      have hnew : N + 1 ∉ Finset.Icc 1 N := by simp
      have hsum : (∑ m ∈ Finset.Icc 1 (N + 1),
          independentCount m / ((m : ℝ) * (m + 1))) =
          (∑ m ∈ Finset.Icc 1 N,
            independentCount m / ((m : ℝ) * (m + 1))) +
            independentCount (N + 1) /
              (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) + 1)) := by
        rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1),
          Finset.sum_insert hnew]
        ring
      rw [independentWeight_succ, ih, hsum]
      simp only [independentCount_succ]
      split_ifs
      all_goals
        norm_num only [Nat.cast_add, Nat.cast_one]
        have h₁ : (N : ℝ) + 1 ≠ 0 := by positivity
        have h₂ : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
        field_simp [h₁, h₂]
        ring

theorem lower_mesh_le_weight (M y : ℕ) (hM : 1 ≤ M) :
    (∑ m ∈ Finset.Ico M y,
      independentCount m / ((m : ℝ) * (m + 1))) ≤ independentWeight y := by
  have hsub : Finset.Ico M y ⊆ Finset.Icc 1 y := by
    intro m hm
    obtain ⟨hMm, hmy⟩ := Finset.mem_Ico.mp hm
    exact Finset.mem_Icc.mpr ⟨le_trans hM hMm, hmy.le⟩
  have hnonneg : ∀ m : ℕ,
      0 ≤ independentCount m / ((m : ℝ) * (m + 1)) := by
    intro m
    exact div_nonneg (independentCount_nonneg m) (by positivity)
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 y,
        independentCount m / ((m : ℝ) * (m + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm hnot
      exact hnonneg m
    _ ≤ independentWeight y := by
      rw [independent_weight_abel]
      exact le_add_of_nonneg_left
        (div_nonneg (independentCount_nonneg y) (by positivity))

theorem finite_weight_lower (N y : ℕ) (a : ℝ)
    (hprime : ∀ m ∈ independentDenominators y,
      a / (m : ℝ) ≤ (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (compatibilityCutoff m)) :
    a * independentWeight y ≤ independentCount N := by
  have hB : ∀ m ∈ independentDenominators y, IndependentDenominator m := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  calc
    a * independentWeight y = ∑ m ∈ independentDenominators y, a / (m : ℝ) := by
      rw [independentWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ ∑ m ∈ independentDenominators y,
        ((Nat.primeCounting (N / m) : ℝ) -
          Nat.primeCounting (compatibilityCutoff m)) := Finset.sum_le_sum hprime
    _ ≤ independentCount N := finite_compatible_prime_recurrence _ N hB

/-- The exact renewal sum to which a uniform prime estimate is applied. -/
theorem finite_lower_mesh (N y M : ℕ) (a : ℝ) (ha : 0 ≤ a) (hM : 1 ≤ M)
    (hprime : ∀ m : ℕ, 1 ≤ m → m ≤ y →
      a / (m : ℝ) ≤ (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (compatibilityCutoff m)) :
    a * (∑ m ∈ Finset.Ico M y,
      independentCount m / ((m : ℝ) * (m + 1))) ≤ independentCount N := by
  calc
    _ ≤ a * independentWeight y :=
      mul_le_mul_of_nonneg_left (lower_mesh_le_weight M y hM) ha
    _ ≤ independentCount N := by
      apply finite_weight_lower
      intro m hm
      obtain ⟨hmI, hgood⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hmI
      exact hprime m hm1 hmy

end Erdos320
