import Erdos320.LowerCompatible
import Mathlib.Tactic.FieldSimp

/-!
An original proof of the compatible-prime multiplication step. A subset of
denominators is partitioned according to divisibility by p. The divisible part
scales to earlier denominators at m, and the remaining part is regular modulo p.
-/

namespace Erdos320

def divisibleQuotients (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.filter (fun n => p ∣ n)).image (fun n => n / p)

def primeFreePart (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun n => ¬p ∣ n)

theorem quotient_injective_on_divisible (p : ℕ) (A : Finset ℕ) :
    Set.InjOn (fun n => n / p) ↑(A.filter (fun n => p ∣ n)) := by
  intro a ha b hb hab
  have haD : p ∣ a := (Finset.mem_filter.mp ha).2
  have hbD : p ∣ b := (Finset.mem_filter.mp hb).2
  change a / p = b / p at hab
  calc
    a = a / p * p := (Nat.div_mul_cancel haD).symm
    _ = b / p * p := by rw [hab]
    _ = b := Nat.div_mul_cancel hbD

theorem reciprocal_divisible_split (p : ℕ) (A : Finset ℕ) :
    (∑ n ∈ A, (n : ℚ)⁻¹) =
      (p : ℚ)⁻¹ * (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) +
        ∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹ := by
  classical
  have himage : (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) =
      ∑ n ∈ A.filter (fun n => p ∣ n), ((n / p : ℕ) : ℚ)⁻¹ := by
    unfold divisibleQuotients
    exact Finset.sum_image (quotient_injective_on_divisible p A)
  have hscaled : (∑ n ∈ A.filter (fun n => p ∣ n), (n : ℚ)⁻¹) =
      (p : ℚ)⁻¹ * (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) := by
    rw [himage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hdiv : p ∣ n := (Finset.mem_filter.mp hn).2
    have hfactor : (n : ℚ) = (p : ℚ) * ((n / p : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    rw [hfactor, mul_inv_rev]
    ring
  calc
    (∑ n ∈ A, (n : ℚ)⁻¹) =
        (∑ n ∈ A.filter (fun n => p ∣ n), (n : ℚ)⁻¹) +
          ∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹ := by
      exact (Finset.sum_filter_add_sum_filter_not A
        (fun n => p ∣ n) (fun n => (n : ℚ)⁻¹)).symm
    _ = _ := by rw [hscaled]

theorem divisibleQuotients_subset {p m : ℕ} (hp : 0 < p)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 (m * p - 1)) :
    divisibleQuotients p A ⊆ Finset.Icc 1 (m - 1) := by
  intro q hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hnA, hpn⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnmax⟩ := Finset.mem_Icc.mp (hA hnA)
  have hpnle : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hq1 : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa)
  have hmp : 0 < m * p := by omega
  have hqM : n / p < m := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    omega
  exact Finset.mem_Icc.mpr ⟨hq1, by omega⟩

theorem divisibleQuotients_sum_mem {p m : ℕ} (hp : 0 < p)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 (m * p - 1)) :
    (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) ∈ sums (m - 1) := by
  apply Finset.mem_image.mpr
  refine ⟨divisibleQuotients p A, ?_, rfl⟩
  exact Finset.mem_powerset.mpr (divisibleQuotients_subset hp hA)

theorem primeFreePart_regular {p : ℕ} (hp : Nat.Prime p)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n) :
    PrimeRegular p (∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹) := by
  apply primeRegular_reciprocal_sum hp
  · intro n hn
    exact hA n (Finset.mem_filter.mp hn).1
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- The compatible-prime construction produces a new independent denominator.
This is the multiplicative mechanism needed for a growing-depth lower bound. -/
theorem compatible_prime_mul_independent {p m : ℕ} (hp : Nat.Prime p)
    (hcompatible : CompatiblePrime p m) : IndependentDenominator (m * p) := by
  refine ⟨Nat.mul_pos hcompatible.1 hp.pos, ?_⟩
  intro a ha b hb heq
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hb
  have hAsub : A ⊆ Finset.Icc 1 (m * p - 1) := Finset.mem_powerset.mp hA
  have hBsub : B ⊆ Finset.Icc 1 (m * p - 1) := Finset.mem_powerset.mp hB
  let a' : ℚ := ∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹
  let b' : ℚ := ∑ n ∈ divisibleQuotients p B, (n : ℚ)⁻¹
  let u : ℚ := ∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹
  let v : ℚ := ∑ n ∈ primeFreePart p B, (n : ℚ)⁻¹
  have ha' : a' ∈ sums (m - 1) := divisibleQuotients_sum_mem hp.pos hAsub
  have hb' : b' ∈ sums (m - 1) := divisibleQuotients_sum_mem hp.pos hBsub
  have hu : PrimeRegular p u := by
    apply primeFreePart_regular hp A
    intro n hn
    exact (Finset.mem_Icc.mp (hAsub hn)).1
  have hv : PrimeRegular p v := by
    apply primeFreePart_regular hp B
    intro n hn
    exact (Finset.mem_Icc.mp (hBsub hn)).1
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcompatible.1)
  have hAeq : (p : ℚ) * (∑ n ∈ A, (n : ℚ)⁻¹) = a' + p * u := by
    rw [reciprocal_divisible_split p A]
    change (p : ℚ) * ((p : ℚ)⁻¹ * a' + u) = a' + p * u
    calc
      _ = ((p : ℚ) * (p : ℚ)⁻¹) * a' + p * u := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp0, one_mul]
  have hBeq : (p : ℚ) * (∑ n ∈ B, (n : ℚ)⁻¹) = b' + p * v := by
    rw [reciprocal_divisible_split p B]
    change (p : ℚ) * ((p : ℚ)⁻¹ * b' + v) = b' + p * v
    calc
      _ = ((p : ℚ) * (p : ℚ)⁻¹) * b' + p * v := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp0, one_mul]
  have hscaled : (p : ℚ) *
      ((∑ n ∈ A, (n : ℚ)⁻¹) - ∑ n ∈ B, (n : ℚ)⁻¹) = (m : ℚ)⁻¹ := by
    rw [heq, Nat.cast_mul]
    field_simp [hp0, hm0]
  have hresidual : (m : ℚ)⁻¹ - (a' - b') = (p : ℚ) * (u - v) := by
    rw [← hscaled, mul_sub, hAeq, hBeq]
    ring
  apply hcompatible.2 a' ha' b' hb'
  rw [hresidual]
  exact prime_dvd_mul_num hp (primeRegular_sub hp hu hv)

end Erdos320
