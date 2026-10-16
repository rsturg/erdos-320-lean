import Erdos320.LowerCutoff
import Mathlib.NumberTheory.PrimeCounting

/-!
Exact finite counting of the independently constructed compatible-prime
products. Each denominator is counted at most once, because its prime factor
strictly exceeds the cofactor. All prime-counting estimates are separate.
-/

namespace Erdos320

def admissiblePrimes (m N : ℕ) : Finset ℕ :=
  (Finset.Ioc (compatibilityCutoff m) (N / m)).filter Nat.Prime

def primeProducts (m N : ℕ) : Finset ℕ :=
  (admissiblePrimes m N).image (fun p => m * p)

theorem primeCounting_le_independent_card (N : ℕ) :
    Nat.primeCounting N ≤ (independentDenominators N).card := by
  have hsub : Nat.primesLE N ⊆ independentDenominators N := by
    intro p hp
    obtain ⟨hpN, hpPrime⟩ := Nat.mem_primesLE.mp hp
    exact primes_in_independentDenominators hpPrime hpN
  simpa using Finset.card_le_card hsub

theorem self_le_compatibilityCutoff (m : ℕ) : m ≤ compatibilityCutoff m := by
  have hf : 1 ≤ m.factorial := Nat.factorial_pos m
  have hmul := Nat.mul_le_mul_left (2 * m) hf
  dsimp [compatibilityCutoff]
  simp only [mul_one] at hmul
  omega

theorem prime_product_unique {m n p q : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hmp : m < p) (hnq : n < q) (heq : m * p = n * q) :
    m = n ∧ p = q := by
  by_cases hpq : p = q
  · subst q
    have hmn : m = n := Nat.eq_of_mul_eq_mul_right hp.pos heq
    exact ⟨hmn, rfl⟩
  · have hnpq : ¬p ∣ q := by
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    have hnqp : ¬q ∣ p := by
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
    have hpn : p ∣ n := by
      apply (hp.dvd_mul.mp ?_).resolve_right hnpq
      rw [← heq]
      exact ⟨m, by ring⟩
    have hqm : q ∣ m := by
      apply (hq.dvd_mul.mp ?_).resolve_right hnqp
      rw [heq]
      exact ⟨n, by ring⟩
    have hpnLe : p ≤ n := Nat.le_of_dvd hn hpn
    have hqmLe : q ≤ m := Nat.le_of_dvd hm hqm
    omega

theorem primeProducts_card {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (primeProducts m N).card = (admissiblePrimes m N).card := by
  unfold primeProducts
  apply Finset.card_image_of_injective
  intro p q heq
  exact Nat.eq_of_mul_eq_mul_left hm heq

theorem primeProducts_subset {m N : ℕ} (hm : IndependentDenominator m) :
    primeProducts m N ⊆ independentDenominators N := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hinterval, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlarge, hpN⟩ := Finset.mem_Ioc.mp hinterval
  have hprod : m * p ≤ N := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm.1).mp hpN
  rw [independentDenominators, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.mul_pos hm.1 hpPrime.pos, hprod⟩,
    independent_mul_large_prime hpPrime hm hlarge⟩

theorem primeProducts_disjoint {m n N : ℕ}
    (hm : IndependentDenominator m) (hn : IndependentDenominator n)
    (hmn : m ≠ n) : Disjoint (primeProducts m N) (primeProducts n N) := by
  rw [Finset.disjoint_left]
  intro d hdm hdn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hdm
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hdn
  obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqI, hqPrime⟩ := Finset.mem_filter.mp hq
  have hmp : m < p := lt_of_le_of_lt (self_le_compatibilityCutoff m)
    (Finset.mem_Ioc.mp hpI).1
  have hnq : n < q := lt_of_le_of_lt (self_le_compatibilityCutoff n)
    (Finset.mem_Ioc.mp hqI).1
  exact hmn (prime_product_unique hm.1 hn.1 hpPrime hqPrime hmp hnq heq.symm).1

theorem sum_admissiblePrimes_card_le (B : Finset ℕ) (N : ℕ)
    (hB : ∀ m ∈ B, IndependentDenominator m) :
    ∑ m ∈ B, (admissiblePrimes m N).card ≤
      (independentDenominators N).card := by
  classical
  have hpair : (B : Set ℕ).PairwiseDisjoint (fun m => primeProducts m N) := by
    intro m hm n hn hmn
    exact primeProducts_disjoint (hB m hm) (hB n hn) hmn
  have hsub : B.biUnion (fun m => primeProducts m N) ⊆ independentDenominators N := by
    intro d hd
    obtain ⟨m, hm, hdm⟩ := Finset.mem_biUnion.mp hd
    exact primeProducts_subset (hB m hm) hdm
  calc
    ∑ m ∈ B, (admissiblePrimes m N).card = ∑ m ∈ B, (primeProducts m N).card := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (primeProducts_card (hB m hm).1 N).symm
    _ = (B.biUnion (fun m => primeProducts m N)).card := (Finset.card_biUnion hpair).symm
    _ ≤ (independentDenominators N).card := Finset.card_le_card hsub

/-- Removing all small primes loses at most their prime count; no ordering
assumption between the two endpoints is required. -/
theorem primeCounting_le_small_add_admissible (m N : ℕ) :
    Nat.primeCounting (N / m) ≤ Nat.primeCounting (compatibilityCutoff m) +
      (admissiblePrimes m N).card := by
  have hsub : Nat.primesLE (N / m) ⊆
      Nat.primesLE (compatibilityCutoff m) ∪ admissiblePrimes m N := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    by_cases hsmall : p ≤ compatibilityCutoff m
    · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hsmall, hp'.2⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hp'.1⟩, hp'.2⟩
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  simpa using hcard

theorem primeCounting_difference_le_admissible (m N : ℕ) :
    (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) ≤
      (admissiblePrimes m N).card := by
  have h : (Nat.primeCounting (N / m) : ℝ) ≤
      (Nat.primeCounting (compatibilityCutoff m) : ℝ) +
        (admissiblePrimes m N).card := by
    exact_mod_cast primeCounting_le_small_add_admissible m N
  linarith

theorem finite_compatible_prime_recurrence (B : Finset ℕ) (N : ℕ)
    (hB : ∀ m ∈ B, IndependentDenominator m) :
    ∑ m ∈ B, ((Nat.primeCounting (N / m) : ℝ) -
      Nat.primeCounting (compatibilityCutoff m)) ≤
        ((independentDenominators N).card : ℝ) := by
  calc
    _ ≤ ∑ m ∈ B, ((admissiblePrimes m N).card : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact primeCounting_difference_le_admissible m N
    _ ≤ ((independentDenominators N).card : ℝ) := by
      exact_mod_cast sum_admissiblePrimes_card_le B N hB

end Erdos320
