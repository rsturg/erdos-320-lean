import Erdos320.UpperFinite.Combinatorics
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
An elementary rational grid bound. The common denominator need not be a
least common multiple. The proofs are independent implementations for this
project of the classical denominator-counting argument.
-/

namespace Erdos320

theorem card_sumsOf_le_common_denominator (A : Finset ℕ) (b : ℕ) (hb : 0 < b)
    (hApos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ b) :
    (sumsOf A).card ≤ b * A.card + 1 := by
  let grid : Finset ℚ := (Finset.range (b * A.card + 1)).image
    (fun a : ℕ => (a : ℚ) / b)
  have hsub : sumsOf A ⊆ grid := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨B, hBA, rfl⟩
    have hBA' : B ⊆ A := Finset.mem_powerset.mp hBA
    let a : ℕ := ∑ n ∈ B, b / n
    have ha : a ≤ b * A.card := by
      calc
        a ≤ ∑ _n ∈ B, b := Finset.sum_le_sum (fun n _ => Nat.div_le_self b n)
        _ = B.card * b := by simp
        _ ≤ A.card * b := Nat.mul_le_mul_right b (Finset.card_le_card hBA')
        _ = b * A.card := Nat.mul_comm _ _
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp [a]
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_div_charZero (hdiv n (hBA' hn))]
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (hApos n (hBA' hn)).ne'
    field_simp [hbQ, hnQ]
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans_eq (Finset.card_range _))

theorem log_card_sumsOf_le_log_common_denominator (A : Finset ℕ) (b : ℕ)
    (hb : 0 < b) (hApos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ b) :
    Real.log ((sumsOf A).card : ℝ) ≤ Real.log (b : ℝ) + Real.log (A.card + 1 : ℕ) := by
  have hcount := card_sumsOf_le_common_denominator A b hb hApos hdiv
  have hsmall : (sumsOf A).card ≤ b * (A.card + 1) := by
    have hb1 : 1 ≤ b := hb
    nlinarith
  have hpos : (0 : ℝ) < (sumsOf A).card := by exact_mod_cast card_sumsOf_pos A
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsuccR : ((A.card + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hlog := Real.log_le_log hpos (show ((sumsOf A).card : ℝ) ≤
      (b : ℝ) * (A.card + 1 : ℕ) by exact_mod_cast hsmall)
  rwa [Real.log_mul hbR hsuccR] at hlog

end Erdos320
