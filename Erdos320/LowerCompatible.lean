import Erdos320.LowerArithmetic
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Int

/-!
Original residue-divisibility implementation of the compatible-prime principle.
The mathematical principle follows Bettin--Grenié--Molteni--Sanna, Section 2.
The arithmetic here uses reduced rational denominators rather than a p-adic
valuation or any external computation.
-/

namespace Erdos320

/-- A rational has a denominator invertible modulo the given prime. -/
def PrimeRegular (p : ℕ) (q : ℚ) : Prop := ¬p ∣ q.den

theorem primeRegular_zero {p : ℕ} (hp : Nat.Prime p) : PrimeRegular p 0 := by
  simpa [PrimeRegular] using hp.not_dvd_one

theorem primeRegular_add {p : ℕ} (hp : Nat.Prime p) {q r : ℚ}
    (hq : PrimeRegular p q) (hr : PrimeRegular p r) :
    PrimeRegular p (q + r) := by
  intro h
  exact hp.not_dvd_lcm hq hr (dvd_trans h (Rat.add_den_dvd_lcm q r))

theorem primeRegular_sub {p : ℕ} (hp : Nat.Prime p) {q r : ℚ}
    (hq : PrimeRegular p q) (hr : PrimeRegular p r) :
    PrimeRegular p (q - r) := by
  intro h
  exact hp.not_dvd_lcm hq hr (dvd_trans h (Rat.sub_den_dvd_lcm q r))

theorem primeRegular_reciprocal_sum {p : ℕ} (hp : Nat.Prime p)
    (A : Finset ℕ) (hpos : ∀ n ∈ A, 0 < n)
    (hunit : ∀ n ∈ A, ¬p ∣ n) :
    PrimeRegular p (∑ n ∈ A, (n : ℚ)⁻¹) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using primeRegular_zero hp
  | @insert n A hn ih =>
      rw [Finset.sum_insert hn]
      apply primeRegular_add hp
      · simpa [PrimeRegular, Rat.inv_natCast_den_of_pos (hpos n (by simp))]
          using hunit n (by simp)
      · apply ih
        · intro a ha
          exact hpos a (by simp [ha])
        · intro a ha
          exact hunit a (by simp [ha])

/-- Multiplying a rational regular at p by p forces p into its numerator. -/
theorem prime_dvd_mul_num {p : ℕ} (hp : Nat.Prime p) {q : ℚ}
    (hq : PrimeRegular p q) : (p : ℤ) ∣ ((p : ℚ) * q).num := by
  have hmul := Rat.mul_num_den' (p : ℚ) q
  simp only [Rat.num_natCast, Rat.den_natCast, Nat.cast_one, mul_one] at hmul
  have hd : (p : ℤ) ∣ ((p : ℚ) * q).num * q.den := by
    rw [hmul]
    exact ⟨q.num * ((p : ℚ) * q).den, by ring⟩
  have hq' : ¬(p : ℤ) ∣ (q.den : ℤ) := by
    simpa only [PrimeRegular, Int.natCast_dvd_natCast] using hq
  exact ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd).resolve_right hq'

/-- A prime is compatible with m if every nonzero signed remainder at m
has numerator nonzero modulo the prime. -/
def CompatiblePrime (p m : ℕ) : Prop :=
  0 < m ∧ ∀ a ∈ sums (m - 1), ∀ b ∈ sums (m - 1),
    ¬(p : ℤ) ∣ ((m : ℚ)⁻¹ - (a - b)).num

theorem compatible_independent {p m : ℕ} (h : CompatiblePrime p m) :
    IndependentDenominator m := by
  refine ⟨h.1, ?_⟩
  intro a ha b hb heq
  have hnot := h.2 a ha b hb
  apply hnot
  rw [heq, sub_self]
  simp

end Erdos320
