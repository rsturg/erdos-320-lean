import Erdos320.Core
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
Original development of the finite lower-bound mechanism for Erdős Problem 320.
The mathematical exact-doubling idea is due to Bleicher--Erdős and is also used
by Bettin--Grenié--Molteni--Sanna. No asymptotic result is asserted in this file.
-/

namespace Erdos320

/-- The translated old support obtained by adjoining denominator `N+1`. -/
def addedLayer (N : ℕ) : Finset ℚ :=
  (sums N).image (fun q => q + ((N + 1 : ℕ) : ℚ)⁻¹)

/-- A positive denominator independent of all signed sums of earlier terms. -/
def IndependentDenominator (d : ℕ) : Prop :=
  0 < d ∧ ∀ a ∈ sums (d - 1), ∀ b ∈ sums (d - 1),
    a - b ≠ (d : ℚ)⁻¹

noncomputable instance (d : ℕ) : Decidable (IndependentDenominator d) :=
  Classical.propDecidable _

/-- Independent denominators among the first `N` positive integers. -/
noncomputable def independentDenominators (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter IndependentDenominator

theorem sumsOf_insert (A : Finset ℕ) {d : ℕ} (hd : d ∉ A) :
    sumsOf (insert d A) =
      sumsOf A ∪ (sumsOf A).image (fun q => q + (d : ℚ)⁻¹) := by
  classical
  unfold sumsOf
  rw [Finset.powerset_insert, Finset.image_union]
  congr 1
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro B hB
  have hdB : d ∉ B := by
    intro h
    exact hd ((Finset.mem_powerset.mp hB) h)
  simp [hdB, add_comm]

theorem sums_succ_decomposition (N : ℕ) :
    sums (N + 1) = sums N ∪ addedLayer N := by
  have hnew : N + 1 ∉ Finset.Icc 1 N := by simp
  unfold sums addedLayer
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1)]
  exact sumsOf_insert _ hnew

theorem addedLayer_card (N : ℕ) : (addedLayer N).card = S N := by
  rw [addedLayer, S]
  exact Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

theorem S_mono_step (N : ℕ) : S N ≤ S (N + 1) := by
  unfold S
  rw [sums_succ_decomposition]
  exact Finset.card_le_card Finset.subset_union_left

theorem S_exact_doubling {d : ℕ} (hd : IndependentDenominator d) :
    S d = 2 * S (d - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd.1)
  have hd' : ∀ a ∈ sums d, ∀ b ∈ sums d,
      a - b ≠ ((d + 1 : ℕ) : ℚ)⁻¹ := by
    simpa using hd.2
  have hdis : Disjoint (sums d) (addedLayer d) := by
    rw [Finset.disjoint_left]
    intro a ha htrans
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp htrans
    exact hd' _ ha _ hb (by ring)
  change (sums (d + 1)).card = 2 * (sums d).card
  rw [sums_succ_decomposition, Finset.card_union_of_disjoint hdis,
    addedLayer_card]
  simp only [S]
  omega

theorem independentDenominators_succ (N : ℕ) :
    independentDenominators (N + 1) =
      if IndependentDenominator (N + 1) then
        insert (N + 1) (independentDenominators N)
      else independentDenominators N := by
  classical
  unfold independentDenominators
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1),
    Finset.filter_insert]

theorem S_zero_eq_one : S 0 = 1 := by
  simp [S, sums, sumsOf]

theorem independent_power_le_S (N : ℕ) :
    2 ^ (independentDenominators N).card ≤ S N := by
  classical
  induction N with
  | zero => simp [independentDenominators, S_zero_eq_one]
  | succ N ih =>
      rw [independentDenominators_succ]
      split_ifs with h
      · have hnew : N + 1 ∉ independentDenominators N := by
          simp [independentDenominators]
        rw [Finset.card_insert_of_notMem hnew, pow_succ, S_exact_doubling h]
        simpa only [Nat.succ_sub_one, Nat.mul_comm] using
          Nat.mul_le_mul_right 2 ih
      · exact le_trans ih (S_mono_step N)

theorem independent_count_log_lower (N : ℕ) :
    ((independentDenominators N).card : ℝ) * Real.log 2 ≤ logS N := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (independentDenominators N).card := by positivity
  have hineq : (2 : ℝ) ^ (independentDenominators N).card ≤ (S N : ℝ) := by
    exact_mod_cast independent_power_le_S N
  have hlog := Real.log_le_log hpow hineq
  simpa [logS, Real.log_pow] using hlog

end Erdos320
