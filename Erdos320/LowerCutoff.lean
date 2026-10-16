import Erdos320.LowerMultiplication
import Mathlib.Tactic.Linarith

/-!
A deliberately coarse, explicit compatibility cutoff. Factorial common
denominators suffice for an independent construction; no published numerical
table or external certificate enters these lemmas.
-/

namespace Erdos320

def compatibilityCutoff (m : ℕ) : ℕ := 2 * m * m.factorial

/-- A coarse exponential bound convenient when the cofactor is at most the
square root of `log N`. -/
theorem compatibilityCutoff_le_two_pow_square (m : ℕ) :
    compatibilityCutoff m ≤ 2 * m * 2 ^ (m * m) := by
  have hm : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    compatibilityCutoff m = 2 * m * m.factorial := rfl
    _ ≤ 2 * m * m ^ m := Nat.mul_le_mul_left _ (Nat.factorial_le_pow m)
    _ ≤ 2 * m * (2 ^ m) ^ m :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm m)
    _ = 2 * m * 2 ^ (m * m) := by rw [pow_mul]

theorem sums_value_bounds {N : ℕ} {q : ℚ} (hq : q ∈ sums N) :
    0 ≤ q ∧ q ≤ (N : ℚ) := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hq
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hA
  have hcard : A.card ≤ N := by
    have h := Finset.card_le_card hsub
    simpa using h
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    positivity
  · calc
      (∑ n ∈ A, (n : ℚ)⁻¹) ≤ ∑ _n ∈ A, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (hsub hn)).1
        exact (inv_le_one₀ (by exact_mod_cast (show 0 < n by omega))).mpr
          (by exact_mod_cast hn1)
      _ = (A.card : ℚ) := by simp
      _ ≤ (N : ℚ) := by exact_mod_cast hcard

theorem remainder_den_dvd_factorial {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (ha : a ∈ sums (m - 1)) (hb : b ∈ sums (m - 1)) :
    ((m : ℚ)⁻¹ - (a - b)).den ∣ m.factorial := by
  have haD : a.den ∣ m.factorial :=
    dvd_trans (sums_den_dvd_factorial ha)
      (Nat.factorial_dvd_factorial (Nat.sub_le m 1))
  have hbD : b.den ∣ m.factorial :=
    dvd_trans (sums_den_dvd_factorial hb)
      (Nat.factorial_dvd_factorial (Nat.sub_le m 1))
  apply dvd_trans (Rat.sub_den_dvd_lcm _ _)
  apply Nat.lcm_dvd
  · rw [Rat.inv_natCast_den_of_pos hm]
    exact Nat.dvd_factorial hm le_rfl
  · exact dvd_trans (Rat.sub_den_dvd_lcm a b) (Nat.lcm_dvd haD hbD)

theorem remainder_abs_le {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (ha : a ∈ sums (m - 1)) (hb : b ∈ sums (m - 1)) :
    |(m : ℚ)⁻¹ - (a - b)| ≤ 2 * (m : ℚ) := by
  obtain ⟨ha0, haM⟩ := sums_value_bounds ha
  obtain ⟨hb0, hbM⟩ := sums_value_bounds hb
  have hm1 : 1 ≤ m := hm
  have hmcast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  rw [hmcast] at haM hbM
  have hmi0 : 0 ≤ (m : ℚ)⁻¹ := by positivity
  have hmi1 : (m : ℚ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by exact_mod_cast hm)).mpr (by exact_mod_cast hm1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem remainder_numerator_bound {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (ha : a ∈ sums (m - 1)) (hb : b ∈ sums (m - 1)) :
    ((m : ℚ)⁻¹ - (a - b)).num.natAbs ≤ compatibilityCutoff m := by
  let q : ℚ := (m : ℚ)⁻¹ - (a - b)
  have hqD : q.den ∣ m.factorial := remainder_den_dvd_factorial hm ha hb
  have hqLe : q.den ≤ m.factorial := Nat.le_of_dvd (Nat.factorial_pos m) hqD
  have habs : |q| ≤ 2 * (m : ℚ) := remainder_abs_le hm ha hb
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrepr : (q.num : ℚ) = q * q.den := (div_eq_iff hd0).mp q.num_div_den
  have hnumQ : (q.num.natAbs : ℚ) ≤ (compatibilityCutoff m : ℚ) := by
    calc
      (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      _ = |q| * (q.den : ℚ) := by
        rw [hrepr, abs_mul]
        exact congrArg (fun t : ℚ => |q| * t)
          (abs_of_nonneg (show (0 : ℚ) ≤ q.den by positivity))
      _ ≤ (2 * (m : ℚ)) * (m.factorial : ℚ) := by
        exact mul_le_mul habs (by exact_mod_cast hqLe) (by positivity) (by positivity)
      _ = (compatibilityCutoff m : ℚ) := by
        simp [compatibilityCutoff, Nat.cast_mul]
  exact_mod_cast hnumQ

theorem compatible_of_gt_cutoff {p m : ℕ} (hm : IndependentDenominator m)
    (hlarge : compatibilityCutoff m < p) : CompatiblePrime p m := by
  refine ⟨hm.1, ?_⟩
  intro a ha b hb hdiv
  let q : ℚ := (m : ℚ)⁻¹ - (a - b)
  have hq0 : q ≠ 0 := by
    intro hz
    exact hm.2 a ha b hb (sub_eq_zero.mp hz).symm
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hnumPos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum0
  have hnatDiv : p ∣ q.num.natAbs := by
    exact_mod_cast (Int.dvd_natAbs.mpr hdiv)
  have hpLe : p ≤ q.num.natAbs := Nat.le_of_dvd hnumPos hnatDiv
  have hbound := remainder_numerator_bound hm.1 ha hb
  change q.num.natAbs ≤ compatibilityCutoff m at hbound
  omega

theorem independent_mul_large_prime {p m : ℕ} (hp : Nat.Prime p)
    (hm : IndependentDenominator m) (hlarge : compatibilityCutoff m < p) :
    IndependentDenominator (m * p) :=
  compatible_prime_mul_independent hp (compatible_of_gt_cutoff hm hlarge)

end Erdos320
