import Erdos320.LowerCutoff
import Erdos320.LogScale
import Erdos320.UpperAnalyticPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Original uniform prime estimates for the compatible-prime lower construction. -/

namespace Erdos320

open Filter

theorem primeCounting_le_argument (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hs : Nat.primesLE n ⊆ Finset.Icc 1 n := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le,
      Nat.le_of_mem_primesLE hp⟩
  simpa using Finset.card_le_card hs

theorem prime_count_common_log_lower {n N : ℕ} {e : ℝ}
    (hn : 2 ≤ n) (hnN : n ≤ N) (hpsi : (n : ℝ) - e ≤ Chebyshev.psi n) :
    ((n : ℝ) - e) / Real.log N ≤ (Nat.primeCounting n : ℝ) := by
  have hN : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN
  apply (div_le_iff₀ hlog).mpr
  calc
    (n : ℝ) - e ≤ Chebyshev.psi n := hpsi
    _ ≤ (Nat.primeCounting n : ℝ) * Real.log n :=
      Chebyshev.psi_le_primeCounting_mul_log n
    _ ≤ (Nat.primeCounting n : ℝ) * Real.log N :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log hn0 (by exact_mod_cast hnN)) (by positivity)

theorem cofactor_quotient_ge_sqrt {N m : ℕ}
    (hN : (4 : ℝ) ≤ N) (hm : 1 ≤ m)
    (hmL : (m : ℝ) ≤ Real.sqrt (Real.log N))
    (hL : Real.log (N : ℝ) ≤ (N : ℝ) / 4) :
    Real.sqrt (N : ℝ) ≤ ((N / m : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by linarith)).le
  have hsL := Real.sq_sqrt hlog
  have hsN := Real.sq_sqrt hN0
  have hsL0 := Real.sqrt_nonneg (Real.log (N : ℝ))
  have hsN0 := Real.sqrt_nonneg (N : ℝ)
  have hm2 : (m : ℝ) ^ 2 ≤ Real.log N := by nlinarith
  have hmul : 2 * Real.sqrt (N : ℝ) * m ≤ N := by
    have htwom : 2 * (m : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
    nlinarith [mul_nonneg hsN0 (sub_nonneg.mpr htwom)]
  have hdivNat : N < (N / m + 1) * m := by
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < m by omega)
  have hdivR : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * m := by exact_mod_cast hdivNat
  have hsN1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
  nlinarith

theorem prime_count_difference_lower {n N b : ℕ} {X e ε : ℝ}
    (hn : 2 ≤ n) (hnN : n ≤ N)
    (hpsi : (n : ℝ) - e ≤ Chebyshev.psi n)
    (hround : X - 1 ≤ (n : ℝ))
    (herror : 1 + e + (b : ℝ) * Real.log N ≤ ε * X) :
    (1 - ε) * X / Real.log N ≤
      (Nat.primeCounting n : ℝ) - Nat.primeCounting b := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := (div_le_iff₀ hlog).mp (prime_count_common_log_lower hn hnN hpsi)
  have hb : (Nat.primeCounting b : ℝ) ≤ b := by exact_mod_cast primeCounting_le_argument b
  apply (div_le_iff₀ hlog).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb hlog.le]

/-- A fully explicit sufficient set of uniform error conditions. The eventual
version below will discharge these from the quantitative PNT and elementary
growth estimates. -/
theorem uniform_prime_difference_of_bounds {N : ℕ} {z : ℝ}
    (hN : (4 : ℝ) ≤ N) (hL : 8 ≤ Real.log (N : ℝ))
    (hLsmall : Real.log (N : ℝ) ≤ (N : ℝ) / 4)
    (hpower : Real.log (N : ℝ) ^ 5 ≤ N)
    (hz : 1 ≤ z) (hzL : z ≤ Real.log (N : ℝ))
    (hcut : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Real.sqrt (Real.log N) →
      (compatibilityCutoff m : ℝ) * m * Real.log N ^ 5 ≤ N)
    (hpnt : ∀ x : ℝ, Real.sqrt (N : ℝ) ≤ x →
      |Chebyshev.psi x - x| ≤ x / Real.log x ^ 6) :
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Real.sqrt (Real.log N) →
      ((1 - 1 / z ^ 2) * ((N : ℝ) + 1) / Real.log N) / m ≤
        (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) := by
  intro m hm hmL
  let L : ℝ := Real.log N
  let n : ℕ := N / m
  let X : ℝ := (N : ℝ) / m
  let e : ℝ := (n : ℝ) / Real.log (n : ℝ) ^ 6
  have hL' : 8 ≤ L := hL
  have hL₀ : 0 < L := by linarith
  have hN₀ : (0 : ℝ) < N := by linarith
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsN := Real.sq_sqrt hN₀.le
  have hsN₀ := Real.sqrt_nonneg (N : ℝ)
  have hnsqrt : Real.sqrt (N : ℝ) ≤ (n : ℝ) :=
    cofactor_quotient_ge_sqrt hN hm hmL hLsmall
  have hnsqrt₂ : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hn : 2 ≤ n := by exact_mod_cast hnsqrt₂.trans hnsqrt
  have hnN : n ≤ N := Nat.div_le_self N m
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn₀ : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogn : L / 2 ≤ Real.log (n : ℝ) := by
    have hh := Real.log_le_log (Real.sqrt_pos.mpr hN₀) hnsqrt
    simpa only [Real.log_sqrt hN₀.le] using hh
  have hL4 : 0 < L ^ 4 := pow_pos hL₀ _
  have hden : L ^ 4 ≤ Real.log (n : ℝ) ^ 6 := by
    have hpre : L ^ 4 ≤ (L / 2) ^ 6 := by
      nlinarith [mul_nonneg (pow_nonneg hL₀.le 4)
        (show 0 ≤ L ^ 2 - 64 by nlinarith)]
    exact hpre.trans (pow_le_pow_left₀ (by linarith) hlogn 6)
  have hnX : (n : ℝ) ≤ X := Nat.cast_div_le
  have he : e ≤ X / L ^ 4 := by
    exact (div_le_div_of_nonneg_left hn₀.le hL4 hden).trans
      (div_le_div_of_nonneg_right hnX hL4.le)
  have hmleL : (m : ℝ) ≤ L := by
    have hsL := Real.sq_sqrt hL₀.le
    have hsL₀ := Real.sqrt_nonneg L
    have : Real.sqrt L ≤ L := by nlinarith
    exact hmL.trans this
  have hfloor : 1 ≤ X / L ^ 4 := by
    apply (le_div_iff₀ hL4).mpr
    apply (le_div_iff₀ hm₀).mpr
    have hh := mul_le_mul_of_nonneg_right hmleL hL4.le
    have hp : L ^ 5 ≤ (N : ℝ) := hpower
    nlinarith only [hh, hp]
  have hcut' : (compatibilityCutoff m : ℝ) * L ≤ X / L ^ 4 := by
    apply (le_div_iff₀ hL4).mpr
    apply (le_div_iff₀ hm₀).mpr
    have hfactor : ((compatibilityCutoff m : ℝ) * L * L ^ 4) * m =
        (compatibilityCutoff m : ℝ) * m * Real.log N ^ 5 := by dsimp [L]; ring
    rw [hfactor]
    exact hcut m hm hmL
  have hpsi : (n : ℝ) - e ≤ Chebyshev.psi n := by
    have hh := (abs_le.mp (hpnt n hnsqrt)).1
    dsimp [e]
    linarith
  have hround : X - 1 ≤ (n : ℝ) := by
    have hh : N < (N / m + 1) * m := by
      simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < m by omega)
    have hhR : (N : ℝ) < ((n : ℝ) + 1) * m := by exact_mod_cast hh
    have : X < (n : ℝ) + 1 := (div_lt_iff₀ hm₀).mpr hhR
    linarith
  have herror : 1 + e + (compatibilityCutoff m : ℝ) * L ≤ (3 / L ^ 4) * X := by
    calc
      _ ≤ X / L ^ 4 + X / L ^ 4 + X / L ^ 4 := add_le_add (add_le_add hfloor he) hcut'
      _ = (3 / L ^ 4) * X := by ring
  have hprime := prime_count_difference_lower hn hnN hpsi hround herror
  have hz₀ : 0 < z := by linarith
  have hreserve : 4 * (1 / L ^ 4) ≤ 1 / z ^ 2 := by
    have hh : 4 / L ^ 4 ≤ 1 / z ^ 2 := by
      apply (div_le_div_iff₀ hL4 (sq_pos_of_pos hz₀)).mpr
      nlinarith [mul_nonneg (sq_nonneg L) (show 0 ≤ L ^ 2 - 4 by nlinarith)]
    simpa only [div_eq_mul_inv, one_mul] using hh
  have hL45 : L ^ 4 ≤ L ^ 5 := by
    exact pow_le_pow_right₀ (show 1 ≤ L by linarith) (by norm_num)
  have hunit : 1 ≤ (N : ℝ) * (1 / L ^ 4) := by
    have hh : L ^ 4 ≤ (N : ℝ) := hL45.trans hpower
    have hr : (1 : ℝ) ≤ (N : ℝ) / L ^ 4 :=
      (le_div_iff₀ hL4).mpr (by simpa only [one_mul] using hh)
    simpa only [div_eq_mul_inv, one_mul] using hr
  have hcompare : (1 - 1 / z ^ 2) * ((N : ℝ) + 1) ≤
      (1 - 3 / L ^ 4) * N := by
    have hh := mul_le_mul_of_nonneg_right hreserve hN₀.le
    have hd : 0 ≤ 1 / z ^ 2 := by positivity
    rw [show 3 / L ^ 4 = 3 * (1 / L ^ 4) by ring]
    nlinarith only [hh, hunit, hd]
  calc
    _ ≤ ((1 - 3 / L ^ 4) * (N : ℝ) / L) / m :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hcompare hL₀.le) hm₀.le
    _ = (1 - 3 / L ^ 4) * X / L := by dsimp [X]; ring
    _ ≤ (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) := hprime

end Erdos320
