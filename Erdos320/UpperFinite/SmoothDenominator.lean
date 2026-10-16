import Erdos320.UpperFinite.Denominator
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr

/-!
A coarse common denominator for the residual prime block. A prime larger
than `sqrt N` can occur only once in a denominator at most `N`. All smaller
prime powers are absorbed by a power of `(sqrt N)!`. This intentionally
coarse construction suffices for a constant-factor upper recursion.
-/

namespace Erdos320

def smoothDenominator (N q : ℕ) : ℕ :=
  primorial q * (Nat.sqrt N).factorial ^ (Nat.log 2 N)

theorem smoothDenominator_pos (N q : ℕ) : 0 < smoothDenominator N q := by
  exact Nat.mul_pos (primorial_pos q) (pow_pos (Nat.factorial_pos _) _)

theorem dvd_smoothDenominator {N q n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ q) :
    n ∣ smoothDenominator N q := by
  apply (Nat.factorization_prime_le_iff_dvd hn.ne' (smoothDenominator_pos N q).ne').mp
  intro p hp
  by_cases hpsmall : p ≤ Nat.sqrt N
  · have hpfact : p ∣ (Nat.sqrt N).factorial := Nat.dvd_factorial hp.pos hpsmall
    have hpfactExp : 1 ≤ ((Nat.sqrt N).factorial).factorization p :=
      hp.dvd_iff_one_le_factorization (Nat.factorial_ne_zero _ ) |>.mp hpfact
    have hexp : n.factorization p ≤ Nat.log 2 N := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc
        2 ^ n.factorization p ≤ p ^ n.factorization p := by gcongr; exact hp.two_le
        _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
        _ ≤ N := hnN
    have hpow : n.factorization p ≤
        ((Nat.sqrt N).factorial ^ (Nat.log 2 N)).factorization p := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      nlinarith
    exact hpow.trans ((Nat.factorization_le_factorization_mul_right
      (primorial_pos q).ne') p)
  · have hexp : n.factorization p ≤ 1 := by
      by_contra h
      have htwo : 2 ≤ n.factorization p := by omega
      have hdvd : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr htwo
      exact hpsmall (Nat.le_sqrt'.mpr ((Nat.le_of_dvd hn hdvd).trans hnN))
    by_cases hpn : p ∣ n
    · have hpprim : p ∣ primorial q := hp.dvd_primorial_iff.mpr (hsmooth p hp hpn)
      have hprimExp : 1 ≤ (primorial q).factorization p :=
        (hp.dvd_iff_one_le_factorization (primorial_pos q).ne').mp hpprim
      exact (hexp.trans hprimExp).trans
        ((Nat.factorization_le_factorization_mul_left
          (pow_ne_zero _ (Nat.factorial_ne_zero _))) p)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact Nat.zero_le _

theorem residualBlock_prime_le (N : ℕ) {n : ℕ}
    (hn : n ∈ residualBlock N (largePrimes N)) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (p : ℝ) ≤ (N : ℝ) / Real.log N := by
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_sdiff.mp hn).1
  have hnN := Finset.mem_Icc.mp hnI
  by_contra h
  have hpP : p ∈ largePrimes N := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le,
      (Nat.le_of_dvd (by omega) hpn).trans hnN.2⟩, hp, lt_of_not_ge h⟩
  apply (Finset.mem_sdiff.mp hn).2
  exact Finset.mem_biUnion.mpr ⟨p, hpP, Finset.mem_filter.mpr ⟨hnI, hpn⟩⟩

theorem residualBlock_dvd_smoothDenominator (N : ℕ) {n : ℕ}
    (hn : n ∈ residualBlock N (largePrimes N)) :
    n ∣ smoothDenominator N ⌊(N : ℝ) / Real.log N⌋₊ := by
  have hnI := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1
  apply dvd_smoothDenominator (by omega) hnI.2
  intro p hp hpn
  exact Nat.le_floor (residualBlock_prime_le N hn hp hpn)

end Erdos320
