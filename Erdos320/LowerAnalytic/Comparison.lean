import Erdos320.LowerAnalytic.Iteration
import Mathlib.Data.Nat.Find

namespace Erdos320.LowerAnalytic

noncomputable def tower (B : ℝ) : ℕ → ℝ
  | 0 => B
  | k + 1 => Real.exp (tower B k)

theorem tower_shift (B : ℝ) (k : ℕ) : tower B (k + 1) = tower (Real.exp B) k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [tower] using congrArg Real.exp ih

theorem iterLog_tower (B : ℝ) (k : ℕ) : iterLog k (tower B k) = B := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iterLog_shift, tower, Real.log_exp]
      exact ih

/-- Adaptive thresholds stay below one ordinary exponential tower with a
larger fixed bottom. Hence the omitted terminal factors stay bounded. -/
theorem cutoff_sq_le_tower {H : ℝ} (hH : 16 ≤ H) (k : ℕ) :
    3 * cutoff H k ^ 2 ≤ tower (3 * H ^ 2) k := by
  have hH1 : 1 ≤ H := by linarith
  induction k with
  | zero => simp [cutoff, tower]
  | succ k ih =>
      have hAk : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
      have he := Real.add_one_le_exp (cutoff H k ^ 2)
      have hthree : 3 ≤ Real.exp (cutoff H k ^ 2) := by nlinarith
      change 3 * Real.exp (cutoff H k ^ 2) ^ 2 ≤ Real.exp (tower (3 * H ^ 2) k)
      calc
        3 * Real.exp (cutoff H k ^ 2) ^ 2 ≤ Real.exp (3 * cutoff H k ^ 2) := by
          rw [show (3 : ℝ) * cutoff H k ^ 2 = (3 : ℕ) * cutoff H k ^ 2 by norm_num,
            Real.exp_nat_mul]
          nlinarith [mul_nonneg (sq_nonneg (Real.exp (cutoff H k ^ 2)))
            (show 0 ≤ Real.exp (cutoff H k ^ 2) - 3 by linarith)]
        _ ≤ _ := Real.exp_le_exp.mpr ih

theorem cutoff_le_tower {H : ℝ} (hH : 16 ≤ H) (k : ℕ) :
    cutoff H k ≤ tower (3 * H ^ 2) k := by
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base (by linarith) k)
  have h := cutoff_sq_le_tower hH k
  nlinarith

theorem exists_adaptive_depth {H x : ℝ} (hH : 1 ≤ H) (hx : H ≤ x) :
    ∃ k : ℕ, cutoff H k ≤ x ∧ x < cutoff H (k + 1) := by
  classical
  let R : ℕ := ⌊x⌋₊
  let k : ℕ := Nat.findGreatest (fun i => cutoff H i ≤ x) R
  have hk : cutoff H k ≤ x := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := fun i => cutoff H i ≤ x) (Nat.zero_le R)
      (show cutoff H 0 ≤ x from hx)
  have hkR : k ≤ R := Nat.findGreatest_le R
  refine ⟨k, hk, ?_⟩
  by_contra hnext
  have hnext' : cutoff H (k + 1) ≤ x := le_of_not_gt hnext
  have hbound : k + 1 ≤ R := by
    by_contra hbound
    have hkEq : k = R := by omega
    have hlarge := cutoff_add_index_le hH (R + 1)
    have hfloor : x < (R : ℝ) + 1 := Nat.lt_floor_add_one x
    rw [hkEq] at hnext'
    push_cast at hlarge
    nlinarith
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hbound hnext'

theorem tail_argument_bounded {H x : ℝ} (hH : 16 ≤ H) {k : ℕ}
    (hlo : cutoff H k ≤ x) (hhi : x ≤ cutoff H (k + 1)) :
    iterLog k x ≤ Real.exp (3 * H ^ 2) := by
  have hH1 : 1 ≤ H := by linarith
  have hpos : ∀ j : ℕ, j < k → 0 < iterLog j x := by
    intro j hj
    exact lt_of_lt_of_le (by linarith : 0 < H)
      (iterLog_ge_base_of_cutoff hH1 k x hlo j (by omega))
  have h := iterLog_mono_of_positive (hhi.trans (cutoff_le_tower hH (k + 1))) hpos
  rw [tower_shift, iterLog_tower] at h
  exact h

theorem stoppedProduct_split (k h : ℕ) (x : ℝ)
    (hactive : ∀ j : ℕ, j < k → Real.exp 3 < iterLog j x) :
    stoppedProduct (k + h) x = logFactors k x * stoppedProduct h (iterLog k x) := by
  induction k generalizing x with
  | zero => simp [logFactors, iterLog]
  | succ k ih =>
      have hx : ¬x ≤ Real.exp 3 := not_le.mpr (hactive 0 (by omega))
      have hnext : ∀ j : ℕ, j < k → Real.exp 3 < iterLog j (Real.log x) := by
        intro j hj
        rw [← iterLog_shift]
        exact hactive (j + 1) (by omega)
      rw [show (k + 1) + h = (k + h) + 1 by omega, stoppedProduct, if_neg hx,
        ih (Real.log x) hnext, logFactors_succ_shift, iterLog_shift]
      ring

theorem stoppedProduct_uniform_bound (B : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℕ, ∀ x : ℝ, x ≤ B → stoppedProduct h x ≤ C := by
  let K : ℕ := ⌈B⌉₊
  refine ⟨stoppedProduct K B, one_le_stoppedProduct K B, ?_⟩
  intro h x hx
  have hBK : B ≤ Real.exp 3 + K := by
    have hceil : B ≤ (K : ℝ) := Nat.le_ceil B
    have he := Real.exp_pos (3 : ℝ)
    linarith
  apply (stoppedProduct_monotone h hx).trans
  by_cases hh : h ≤ K
  · exact stoppedProduct_mono_height hh B
  · exact (stoppedProduct_stable_of_input_le hBK (le_of_not_ge hh)).le

theorem full_product_le_partial {H x : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (C : ℝ) (hC : 1 ≤ C)
    (hbound : ∀ h : ℕ, ∀ u : ℝ, u ≤ Real.exp (3 * H ^ 2) → stoppedProduct h u ≤ C)
    {k : ℕ} (hlo : cutoff H k ≤ x) (hhi : x ≤ cutoff H (k + 1)) (h : ℕ) :
    stoppedProduct h x ≤ C * logFactors k x := by
  have hH1 : 1 ≤ H := by linarith
  have hHexp : Real.exp 3 < H := by
    have h := Real.exp_lt_exp.mpr (show (3 : ℝ) < Real.log H by linarith)
    simpa [Real.exp_log (show 0 < H by linarith)] using h
  have hactive : ∀ j : ℕ, j < k → Real.exp 3 < iterLog j x := by
    intro j hj
    exact hHexp.trans_le (iterLog_ge_base_of_cutoff hH1 k x hlo j (by omega))
  have hQ0 : 0 ≤ logFactors k x := by
    unfold logFactors
    apply Finset.prod_nonneg
    intro j hj
    have h := iterLog_ge_base_of_cutoff hH1 k x hlo (j + 1)
      (by have := Finset.mem_range.mp hj; omega)
    linarith
  have htail := tail_argument_bounded hH hlo hhi
  by_cases hkh : k ≤ h
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkh
    rw [stoppedProduct_split k r x hactive]
    have h := mul_le_mul_of_nonneg_left (hbound r (iterLog k x) htail) hQ0
    simpa [mul_comm] using h
  · have hhk : h ≤ k := le_of_lt (lt_of_not_ge hkh)
    have hsplit := stoppedProduct_split k 0 x hactive
    simp only [Nat.add_zero, stoppedProduct, mul_one] at hsplit
    calc
      stoppedProduct h x ≤ stoppedProduct k x := stoppedProduct_mono_height hhk x
      _ = logFactors k x := hsplit
      _ ≤ C * logFactors k x := by nlinarith

theorem exists_full_product_comparison {H : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, H ≤ x →
      ∃ k : ℕ, cutoff H k ≤ x ∧ ∀ h : ℕ, stoppedProduct h x ≤ C * logFactors k x := by
  obtain ⟨C, hC, hbound⟩ := stoppedProduct_uniform_bound (Real.exp (3 * H ^ 2))
  refine ⟨C, hC, ?_⟩
  intro x hx
  obtain ⟨k, hlo, hhi⟩ := exists_adaptive_depth (show 1 ≤ H by linarith) hx
  exact ⟨k, hlo, fun h => full_product_le_partial hH hlogH C hC hbound hlo hhi.le h⟩

end Erdos320.LowerAnalytic
