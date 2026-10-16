import Erdos320.Core
import Mathlib.Data.Finset.NAry
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Positivity

/-!
Finite covering bounds used in the prime-block argument of Luo, Yang, and Zhu,
building on Bleicher and Erdős. The Lean proofs in this file were developed
independently for the project commissioned by Riley Sturgill.
-/

namespace Erdos320

theorem zero_mem_sumsOf (A : Finset ℕ) : (0 : ℚ) ∈ sumsOf A := by
  exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (by simp), by simp⟩

theorem card_sumsOf_pos (A : Finset ℕ) : 0 < (sumsOf A).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_sumsOf A⟩

theorem sumsOf_mono {A B : Finset ℕ} (h : A ⊆ B) : sumsOf A ⊆ sumsOf B := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨C, hC, rfl⟩
  exact Finset.mem_image.mpr ⟨C,
    Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hC).trans h), rfl⟩

/-- Overlapping sets are allowed: allocate an intersection to the first set. -/
theorem card_sumsOf_union_le (A B : Finset ℕ) :
    (sumsOf (A ∪ B)).card ≤ (sumsOf A).card * (sumsOf B).card := by
  apply le_trans (Finset.card_le_card ?_)
    (Finset.card_image₂_le (fun x y : ℚ => x + y) (sumsOf A) (sumsOf B))
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨C, hC, rfl⟩
  have hCA : C ∩ A ⊆ A := Finset.inter_subset_right
  have hCB : C \ A ⊆ B := by
    intro n hn
    rcases Finset.mem_sdiff.mp hn with ⟨hnC, hnA⟩
    exact (Finset.mem_union.mp ((Finset.mem_powerset.mp hC) hnC)).resolve_left hnA
  apply Finset.mem_image₂.mpr
  refine ⟨∑ n ∈ C ∩ A, (n : ℚ)⁻¹, ?_, ∑ n ∈ C \ A, (n : ℚ)⁻¹, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨C ∩ A, Finset.mem_powerset.mpr hCA, rfl⟩
  · exact Finset.mem_image.mpr ⟨C \ A, Finset.mem_powerset.mpr hCB, rfl⟩
  · exact Finset.sum_inter_add_sum_sdiff C A (fun n => (n : ℚ)⁻¹)

theorem card_sumsOf_biUnion_le {ι : Type*} (P : Finset ι) (B : ι → Finset ℕ) :
    (sumsOf (P.biUnion B)).card ≤ ∏ p ∈ P, (sumsOf (B p)).card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [sumsOf]
  | @insert p P hp ih =>
      rw [Finset.biUnion_insert, Finset.prod_insert hp]
      exact (card_sumsOf_union_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem card_sumsOf_cover_le {ι : Type*} (P : Finset ι) (B : ι → Finset ℕ)
    (A Z : Finset ℕ) (hcover : A ⊆ Z ∪ P.biUnion B) :
    (sumsOf A).card ≤ (sumsOf Z).card * ∏ p ∈ P, (sumsOf (B p)).card := by
  exact (Finset.card_le_card (sumsOf_mono hcover)).trans
    ((card_sumsOf_union_le _ _).trans
      (Nat.mul_le_mul_left _ (card_sumsOf_biUnion_le P B)))

/-- The reciprocal values from a dilated denominator set are scaled by `1/p`. -/
theorem sumsOf_mul_image (A : Finset ℕ) {p : ℕ} (hp : p ≠ 0) :
    sumsOf (A.image (fun n => p * n)) =
      (sumsOf A).image (fun q => (p : ℚ)⁻¹ * q) := by
  simp only [sumsOf, Finset.powerset_image, Finset.image_image]
  apply Finset.image_congr
  intro B hB
  change (∑ n ∈ B.image (fun n => p * n), (n : ℚ)⁻¹) =
    (p : ℚ)⁻¹ * ∑ n ∈ B, (n : ℚ)⁻¹
  rw [Finset.sum_image]
  · simp only [Nat.cast_mul, mul_inv_rev, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  · intro a ha b hb hab
    exact mul_left_cancel₀ hp hab

theorem card_sumsOf_mul_image (A : Finset ℕ) {p : ℕ} (hp : p ≠ 0) :
    (sumsOf (A.image (fun n => p * n))).card = (sumsOf A).card := by
  rw [sumsOf_mul_image A hp]
  apply Finset.card_image_of_injective
  apply mul_right_injective₀
  exact inv_ne_zero (by exact_mod_cast hp)

/-- Denominators at most `N` divisible by `p`. -/
def primeBlock (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => p ∣ n)

theorem primeBlock_eq_image (N : ℕ) {p : ℕ} (hp : 0 < p) :
    primeBlock N p = (Finset.Icc 1 (N / p)).image (fun n => p * n) := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, m, rfl⟩
    rcases Finset.mem_Icc.mp hnI with ⟨hlo, hhi⟩
    have hm : 1 ≤ m := by
      by_contra h
      have hm0 : m = 0 := by omega
      simp [hm0] at hlo
    exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr
      ⟨hm, (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hhi)⟩, rfl⟩
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    rcases Finset.mem_Icc.mp hm with ⟨hmlo, hmhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right p m⟩
    · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne' (by omega))
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmhi

theorem card_sumsOf_primeBlock (N : ℕ) {p : ℕ} (hp : 0 < p) :
    (sumsOf (primeBlock N p)).card = S (N / p) := by
  rw [primeBlock_eq_image N hp, card_sumsOf_mul_image _ hp.ne']
  rfl

/-- Residual set after any chosen positive divisor blocks have been removed. -/
def residualBlock (N : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N) \ P.biUnion (primeBlock N)

theorem finite_block_product_bound (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    S N ≤ (sumsOf (residualBlock N P)).card * ∏ p ∈ P, S (N / p) := by
  have hcover : Finset.Icc 1 N ⊆
      residualBlock N P ∪ P.biUnion (primeBlock N) := by
    intro n hn
    by_cases hm : n ∈ P.biUnion (primeBlock N)
    · exact Finset.mem_union_right _ hm
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hn, hm⟩)
  have h := card_sumsOf_cover_le P (primeBlock N) (Finset.Icc 1 N)
    (residualBlock N P) hcover
  change S N ≤ _ at h
  have heq : (∏ p ∈ P, (sumsOf (primeBlock N p)).card) =
      ∏ p ∈ P, S (N / p) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact card_sumsOf_primeBlock N (hP p hp)
  rw [heq] at h
  exact h

theorem finite_block_log_bound (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    logS N ≤ Real.log ((sumsOf (residualBlock N P)).card : ℝ) +
      ∑ p ∈ P, logS (N / p) := by
  have hcount := finite_block_product_bound N P hP
  have hSpos : (0 : ℝ) < S N := by
    exact_mod_cast card_sumsOf_pos (Finset.Icc 1 N)
  have hzpos : (0 : ℝ) < (sumsOf (residualBlock N P)).card := by
    exact_mod_cast card_sumsOf_pos (residualBlock N P)
  have hpPos : ∀ p ∈ P, (0 : ℝ) < S (N / p) := by
    intro p hp
    exact_mod_cast card_sumsOf_pos (Finset.Icc 1 (N / p))
  have hprodPos : 0 < ∏ p ∈ P, (S (N / p) : ℝ) := Finset.prod_pos hpPos
  have hreal : (S N : ℝ) ≤ (sumsOf (residualBlock N P)).card *
      ∏ p ∈ P, (S (N / p) : ℝ) := by exact_mod_cast hcount
  have hlog := Real.log_le_log hSpos hreal
  rw [Real.log_mul hzpos.ne' hprodPos.ne', Real.log_prod (fun p hp => (hpPos p hp).ne')] at hlog
  exact hlog

end Erdos320
