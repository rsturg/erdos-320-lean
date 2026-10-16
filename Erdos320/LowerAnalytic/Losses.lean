import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Summable depth losses for the independent lower renewal argument. These are
elementary uniform estimates, rather than fixed-depth asymptotics.
-/

namespace Erdos320.LowerAnalytic

noncomputable def epsilon (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ (k + 3)

noncomputable def iterationLoss (k : ℕ) : ℝ := 2 * (k + 2 : ℕ) * epsilon k

noncomputable def coefficient (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - iterationLoss i)

theorem epsilon_pos (k : ℕ) : 0 < epsilon k := by
  unfold epsilon
  positivity

theorem epsilon_le (k : ℕ) : epsilon k ≤ 1 / 64 := by
  have hp : (1 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold epsilon
  rw [pow_add]
  norm_num
  nlinarith

theorem epsilon_succ (k : ℕ) : epsilon (k + 1) = epsilon k / 4 := by
  unfold epsilon
  rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
  ring

private theorem index_le_two_pow (k : ℕ) : (k + 2 : ℕ) ≤ (2 : ℝ) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at ih ⊢
      rw [pow_succ]
      nlinarith

theorem iterationLoss_nonneg (k : ℕ) : 0 ≤ iterationLoss k := by
  unfold iterationLoss
  exact mul_nonneg (by positivity) (epsilon_pos k).le

theorem iterationLoss_le_geometric (k : ℕ) :
    iterationLoss k ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hindex := index_le_two_pow k
  have heq : 2 * (2 : ℝ) ^ (k + 1) * (1 / 4 : ℝ) ^ (k + 3) =
      (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
    calc
      2 * (2 : ℝ) ^ (k + 1) * (1 / 4 : ℝ) ^ (k + 3) =
          (1 / 16 : ℝ) * ((2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) := by
        rw [pow_succ, pow_add]
        norm_num
        ring
      _ = _ := by rw [← mul_pow]; norm_num
  unfold iterationLoss epsilon
  rw [← heq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hindex (by norm_num))
    (by positivity)

theorem iterationLoss_le (k : ℕ) : iterationLoss k ≤ 1 / 16 := by
  have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := iterationLoss_le_geometric k
  nlinarith

theorem sum_iterationLoss_le (k : ℕ) :
    (∑ i ∈ Finset.range k, iterationLoss i) ≤ 1 / 8 := by
  calc
    (∑ i ∈ Finset.range k, iterationLoss i) ≤
        ∑ i ∈ Finset.range k, (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => iterationLoss_le_geometric i)
    _ = (1 / 16 : ℝ) * ∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 16 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by norm_num)
    _ = 1 / 8 := by norm_num

private theorem one_sub_sum_le_product (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi := hf i (by simp)
      have hfs : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : 0 ≤ ∑ j ∈ s, f j :=
        Finset.sum_nonneg (fun j hj => (hfs j hj).1)
      have hmul := mul_le_mul_of_nonneg_left (ih hfs) (show 0 ≤ 1 - f i by linarith)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      nlinarith [mul_nonneg hfi.1 hsum]

theorem coefficient_lower (k : ℕ) : 7 / 8 ≤ coefficient k := by
  have h := one_sub_sum_le_product (Finset.range k) iterationLoss
    (fun i _ => ⟨iterationLoss_nonneg i, (iterationLoss_le i).trans (by norm_num)⟩)
  have hsum := sum_iterationLoss_le k
  unfold coefficient
  linarith

theorem coefficient_pos (k : ℕ) : 0 < coefficient k :=
  lt_of_lt_of_le (by norm_num) (coefficient_lower k)

theorem coefficient_le_one (k : ℕ) : coefficient k ≤ 1 := by
  unfold coefficient
  exact Finset.prod_le_one (fun i _ => by have := iterationLoss_le i; linarith)
    (fun i _ => by have := iterationLoss_nonneg i; linarith)

theorem coefficient_zero : coefficient 0 = 1 := by simp [coefficient]

theorem coefficient_succ (k : ℕ) :
    coefficient (k + 1) = coefficient k * (1 - iterationLoss k) := by
  simp [coefficient, Finset.prod_range_succ]

/-- All multiplicative losses of one analytic step have a summable deficit. -/
theorem analytic_step_factor_lower (k : ℕ) :
    1 - iterationLoss k ≤
      (1 - epsilon k) * (1 - 2 * epsilon k) * (1 - epsilon k) ^ k := by
  have he := epsilon_le k
  have he0 := (epsilon_pos k).le
  have hb : 0 ≤ 1 - 2 * epsilon k := by linarith
  have ha : 0 ≤ 1 - epsilon k := by linarith
  have hbern := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ -2 * epsilon k by linarith) (k + 2)
  rw [show 1 + -2 * epsilon k = 1 - 2 * epsilon k by ring] at hbern
  have hfirst : 1 - iterationLoss k ≤ (1 - 2 * epsilon k) ^ (k + 2) := by
    dsimp [iterationLoss]
    push_cast at hbern ⊢
    nlinarith
  apply hfirst.trans
  calc
    (1 - 2 * epsilon k) ^ (k + 2) =
        (1 - 2 * epsilon k) ^ k * (1 - 2 * epsilon k) ^ 2 := by rw [pow_add]
    _ ≤ (1 - epsilon k) ^ k * ((1 - epsilon k) * (1 - 2 * epsilon k)) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ hb (by linarith) _
      · rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by linarith) hb
      · positivity
      · positivity
    _ = _ := by ring

end Erdos320.LowerAnalytic
