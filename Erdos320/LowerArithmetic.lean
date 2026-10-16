import Erdos320.LowerFinite
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Rat.Lemmas

/-!
Common denominators for the independently developed lower-bound construction.
The elementary fact that every prime is an independent denominator is included
as a base case, not as a claim to establish the full asymptotic lower bound.
-/

namespace Erdos320

/-- If every denominator divides `D`, the reduced denominator of the sum does
as well. Working with reduced rational denominators avoids choosing a signed
integer numerator for each subset sum. -/
theorem reciprocal_sum_den_dvd (A : Finset ℕ) (D : ℕ)
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ D) :
    (∑ n ∈ A, (n : ℚ)⁻¹).den ∣ D := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert n A hn ih =>
      have hnpos : 0 < n := hpos n (by simp)
      have hndiv : n ∣ D := hdiv n (by simp)
      have hApos : ∀ a ∈ A, 0 < a := by
        intro a ha
        exact hpos a (by simp [ha])
      have hAdiv : ∀ a ∈ A, a ∣ D := by
        intro a ha
        exact hdiv a (by simp [ha])
      rw [Finset.sum_insert hn]
      apply dvd_trans (Rat.add_den_dvd_lcm _ _)
      exact Nat.lcm_dvd
        (by simpa [Rat.inv_natCast_den_of_pos hnpos] using hndiv)
        (ih hApos hAdiv)

/-- Every reciprocal subset sum from the first `N` denominators has a
reduced denominator dividing `N!`. -/
theorem sums_den_dvd_factorial {N : ℕ} {q : ℚ} (hq : q ∈ sums N) :
    q.den ∣ N.factorial := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hq
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hA
  apply reciprocal_sum_den_dvd
  · intro n hn
    exact (Finset.mem_Icc.mp (hsub hn)).1
  · intro n hn
    have h := Finset.mem_Icc.mp (hsub hn)
    exact Nat.dvd_factorial h.1 h.2

theorem prime_independent {p : ℕ} (hp : Nat.Prime p) :
    IndependentDenominator p := by
  refine ⟨hp.pos, ?_⟩
  intro a ha b hb heq
  have haD := sums_den_dvd_factorial ha
  have hbD := sums_den_dvd_factorial hb
  have hd : (a - b).den ∣ (p - 1).factorial :=
    dvd_trans (Rat.sub_den_dvd_lcm _ _) (Nat.lcm_dvd haD hbD)
  rw [heq, Rat.inv_natCast_den_of_pos hp.pos] at hd
  have hple : p ≤ p - 1 := hp.dvd_factorial.mp hd
  have hpPos := hp.pos
  omega

theorem primes_in_independentDenominators {p N : ℕ}
    (hp : Nat.Prime p) (hpN : p ≤ N) :
    p ∈ independentDenominators N := by
  simp only [independentDenominators, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.one_lt.le, hpN⟩, prime_independent hp⟩

end Erdos320
