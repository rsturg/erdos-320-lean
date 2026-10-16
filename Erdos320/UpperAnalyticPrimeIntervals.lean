import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith

/-!
Original bridge from a quantitative Chebyshev-psi estimate to upper bounds for
prime blocks. It uses nonnegativity of the von Mangoldt function and therefore
does not need a separate quantitative prime-counting / logarithmic-integral
theorem.
-/

namespace Erdos320

/-- Each prime in `(a,b]` supplies at least `log a` to the positive increment
of Chebyshev's psi function. -/
theorem prime_card_mul_log_le_psi_sub
    (P : Finset ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (P.card : ℝ) * Real.log a ≤ Chebyshev.psi b - Chebyshev.psi a := by
  classical
  let Q : Finset ℕ := Finset.Ioc 0 ⌊a⌋₊
  let R : Finset ℕ := Finset.Ioc 0 ⌊b⌋₊
  have hb : 0 ≤ b := ha.le.trans hab
  have hQR : Q ⊆ R := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn'.1, hn'.2.trans (Nat.floor_mono hab)⟩
  have hPR : P ⊆ R := by
    intro p hp
    have h := hP p hp
    apply Finset.mem_Ioc.mpr
    exact ⟨h.1.pos, (Nat.le_floor_iff hb).mpr h.2.2⟩
  have hdis : Disjoint Q P := by
    apply Finset.disjoint_left.mpr
    intro p hpQ hpP
    have hpa : (p : ℝ) ≤ a :=
      (Nat.le_floor_iff ha.le).mp (Finset.mem_Ioc.mp hpQ).2
    exact (not_lt_of_ge hpa) (hP p hpP).2.1
  have hsum :
      (∑ n ∈ Q, ArithmeticFunction.vonMangoldt n) +
          ∑ p ∈ P, ArithmeticFunction.vonMangoldt p ≤
        ∑ n ∈ R, ArithmeticFunction.vonMangoldt n := by
    rw [← Finset.sum_union hdis]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.union_subset hQR hPR
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hlog : (P.card : ℝ) * Real.log a ≤
      ∑ p ∈ P, ArithmeticFunction.vonMangoldt p := by
    calc
      (P.card : ℝ) * Real.log a = ∑ _p ∈ P, Real.log a := by simp
      _ ≤ ∑ p ∈ P, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log ha (hP p hp).2.1.le
      _ = ∑ p ∈ P, ArithmeticFunction.vonMangoldt p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (ArithmeticFunction.vonMangoldt_apply_prime (hP p hp).1).symm
  change Chebyshev.psi a +
      ∑ p ∈ P, ArithmeticFunction.vonMangoldt p ≤ Chebyshev.psi b at hsum
  linarith

/-- A generic endpoint-error version, directly usable with a quantitative PNT.
The errors at the two endpoints may be different. -/
theorem prime_card_le_of_psi_endpoint_errors
    (P : Finset ℕ) (a b eₐ e_b : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hₐ : |Chebyshev.psi a - a| ≤ eₐ)
    (h_b : |Chebyshev.psi b - b| ≤ e_b) :
    (P.card : ℝ) ≤ (b - a + eₐ + e_b) / Real.log a := by
  have hlog : 0 < Real.log a := Real.log_pos ha
  have hcount := prime_card_mul_log_le_psi_sub P a b (by linarith) hab hP
  have hupper : Chebyshev.psi b - b ≤ e_b := (le_abs_self _).trans h_b
  have hlower : -(Chebyshev.psi a - a) ≤ eₐ := (neg_le_abs _).trans hₐ
  apply (le_div_iff₀ hlog).mpr
  linarith

end Erdos320
