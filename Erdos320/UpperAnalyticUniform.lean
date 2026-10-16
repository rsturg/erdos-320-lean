import Erdos320.UpperAnalyticKernel
import Erdos320.UpperAnalyticPrimeIntervals
import Mathlib.Tactic.FieldSimp

/-!
Original uniform prime-interval normalization. The endpoint hypotheses are the
concrete estimates supplied by the quantitative PNT, rather than a prime-counting
axiom. Their consequence has leading coefficient one plus a vanishing error.
-/

namespace Erdos320

theorem prime_interval_normalized_of_endpoint_errors
    (P : Finset ℕ) (X L m u : ℝ)
    (hX : 0 < X) (hL : 0 < L) (hm : 0 < m)
    (hu : 0 ≤ u) (hu_half : u ≤ L / 2)
    (hlogₐ : L - u ≤ Real.log (X / (m + 1)))
    (hlog_b : L / 2 ≤ Real.log (X / m))
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X / (m + 1) < (p : ℝ) ∧ (p : ℝ) ≤ X / m)
    (hₐ : |Chebyshev.psi (X / (m + 1)) - X / (m + 1)| ≤
      (X / (m + 1)) / Real.log (X / (m + 1)) ^ 4)
    (h_b : |Chebyshev.psi (X / m) - X / m| ≤
      (X / m) / Real.log (X / m) ^ 4) :
    (L / X) * (P.card : ℝ) ≤
      (1 + 2 * (u / L) + 64 * (m + 1) / L ^ 4) / (m * (m + 1)) := by
  have hm₁ : 0 < m + 1 := by linarith
  have ha₀ : 0 < X / (m + 1) := div_pos hX hm₁
  have hb₀ : 0 < X / m := div_pos hX hm
  have hab : X / (m + 1) ≤ X / m :=
    div_le_div_of_nonneg_left hX.le hm (by linarith)
  have hla : L / 2 ≤ Real.log (X / (m + 1)) := by linarith
  have hhalf : 0 < L / 2 := by positivity
  have hea : (X / (m + 1)) / Real.log (X / (m + 1)) ^ 4 ≤
      16 * (X / m) / L ^ 4 := by
    calc
      _ ≤ (X / m) / Real.log (X / (m + 1)) ^ 4 :=
        div_le_div_of_nonneg_right hab (pow_nonneg (by linarith) _)
      _ ≤ (X / m) / (L / 2) ^ 4 :=
        div_le_div_of_nonneg_left hb₀.le (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hla 4)
      _ = 16 * (X / m) / L ^ 4 := by ring
  have heb : (X / m) / Real.log (X / m) ^ 4 ≤
      16 * (X / m) / L ^ 4 := by
    calc
      _ ≤ (X / m) / (L / 2) ^ 4 :=
        div_le_div_of_nonneg_left hb₀.le (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hlog_b 4)
      _ = 16 * (X / m) / L ^ 4 := by ring
  have hmass := prime_card_mul_log_le_psi_sub P (X / (m + 1)) (X / m) ha₀ hab hP
  have hpa := (neg_le_abs (Chebyshev.psi (X / (m + 1)) - X / (m + 1))).trans hₐ
  have hpb := (le_abs_self (Chebyshev.psi (X / m) - X / m)).trans h_b
  have hcard₀ : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hmass' : (P.card : ℝ) * (L - u) ≤
      X / m - X / (m + 1) + 32 * (X / m) / L ^ 4 := by
    have hlogmul := mul_le_mul_of_nonneg_left hlogₐ hcard₀
    calc
      _ ≤ (P.card : ℝ) * Real.log (X / (m + 1)) := hlogmul
      _ ≤ Chebyshev.psi (X / m) - Chebyshev.psi (X / (m + 1)) := hmass
      _ ≤ X / m - X / (m + 1) +
          ((X / (m + 1)) / Real.log (X / (m + 1)) ^ 4 +
            (X / m) / Real.log (X / m) ^ 4) := by linarith only [hpa, hpb]
      _ ≤ X / m - X / (m + 1) +
          (16 * (X / m) / L ^ 4 + 16 * (X / m) / L ^ 4) :=
        add_le_add le_rfl (add_le_add hea heb)
      _ = _ := by ring
  let H : ℝ := X / (m * (m + 1))
  let z : ℝ := u / L
  let e : ℝ := 32 * (m + 1) / L ^ 4
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hz : 0 ≤ z := div_nonneg hu hL.le
  have hz_half : z ≤ 1 / 2 := by
    dsimp [z]
    apply (div_le_iff₀ hL).mpr
    linarith
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hleft : (P.card : ℝ) * L * (1 - z) = (P.card : ℝ) * (L - u) := by
    dsimp [z]
    field_simp
  have hright : H * (1 + e) =
      X / m - X / (m + 1) + 32 * (X / m) / L ^ 4 := by
    dsimp [H, e]
    field_simp
    ring
  have hnormalized : (P.card : ℝ) * L ≤ H * (1 + 2 * z + 2 * e) :=
    denominator_loss_normalization hH hz hz_half he (by rw [hleft, hright]; exact hmass')
  have hdiv : ((P.card : ℝ) * L) / X ≤
      (1 + 2 * z + 2 * e) / (m * (m + 1)) := by
    apply (div_le_iff₀ hX).mpr
    calc
      _ ≤ H * (1 + 2 * z + 2 * e) := hnormalized
      _ = _ := by dsimp [H]; ring
  calc
    (L / X) * (P.card : ℝ) = ((P.card : ℝ) * L) / X := by ring
    _ ≤ (1 + 2 * z + 2 * e) / (m * (m + 1)) := hdiv
    _ = _ := by dsimp [z, e]; ring

/-- The preceding estimate is uniform for `m ≤ L`, with an error depending only
on `L,u`. -/
theorem prime_interval_normalized_uniform
    (P : Finset ℕ) (X L m u : ℝ)
    (hX : 0 < X) (hL : 1 ≤ L) (hm : 0 < m) (hmL : m ≤ L)
    (hu : 0 ≤ u) (hu_half : u ≤ L / 2)
    (hlogₐ : L - u ≤ Real.log (X / (m + 1)))
    (hlog_b : L / 2 ≤ Real.log (X / m))
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X / (m + 1) < (p : ℝ) ∧ (p : ℝ) ≤ X / m)
    (hₐ : |Chebyshev.psi (X / (m + 1)) - X / (m + 1)| ≤
      (X / (m + 1)) / Real.log (X / (m + 1)) ^ 4)
    (h_b : |Chebyshev.psi (X / m) - X / m| ≤
      (X / m) / Real.log (X / m) ^ 4) :
    (L / X) * (P.card : ℝ) ≤
      (1 + (2 * (u / L) + 128 / L ^ 3)) / (m * (m + 1)) := by
  have hL₀ : 0 < L := by linarith
  have hterm : 64 * (m + 1) / L ^ 4 ≤ 128 / L ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hL₀ 4) (pow_pos hL₀ 3)).mpr
    have hm₂ : m + 1 ≤ 2 * L := by linarith
    have hpow : 0 ≤ L ^ 3 := (pow_pos hL₀ 3).le
    nlinarith only [mul_le_mul_of_nonneg_right hm₂ hpow]
  have h := prime_interval_normalized_of_endpoint_errors P X L m u hX hL₀ hm hu hu_half
    hlogₐ hlog_b hP hₐ h_b
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ m * (m + 1))
  linarith

end Erdos320
