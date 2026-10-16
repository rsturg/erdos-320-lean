import Erdos320.UpperAnalytic
import Erdos320.LogScale
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The exact normalized recurrence implies the full, growing-depth upper scale.
This file isolates that implication; it does not assert the number-theoretic
recurrence without a proof.
-/

namespace Erdos320

noncomputable def logarithmicWeight (n : ℕ) : ℝ :=
  stoppedProduct n (Real.log (Real.log (n : ℝ)))

noncomputable def normalizedEntropy (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) / (n : ℝ)) * logS n

theorem logarithmicWeight_one_le (n : ℕ) : 1 ≤ logarithmicWeight n :=
  one_le_stoppedProduct n _

theorem logarithmicWeight_monotone : Monotone logarithmicWeight := by
  intro a b hab
  by_cases ha : 2 ≤ a
  · have ha₁ : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
    have ha₀ : (0 : ℝ) < a := by linarith
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
      Real.log_le_log ha₀ habR
    have hloglog : Real.log (Real.log (a : ℝ)) ≤
        Real.log (Real.log (b : ℝ)) :=
      Real.log_le_log (Real.log_pos ha₁) hlog
    exact (stoppedProduct_mono_height hab _).trans
      (stoppedProduct_monotone b hloglog)
  · have ha' : a = 0 ∨ a = 1 := by omega
    rcases ha' with rfl | rfl
    · exact logarithmicWeight_one_le b
    · have h₁ : logarithmicWeight 1 = 1 := by
        simp [logarithmicWeight, stoppedProduct, (Real.exp_pos (3 : ℝ)).le]
      rw [h₁]
      exact logarithmicWeight_one_le b

/-- The exact logarithmic renewal recurrence, once proved, controls the complete
terminal product with one positive constant. No fixed iteration depth is used.
-/
theorem eventual_upper_bound_of_normalized_recurrence
    (A : ℝ) (hA : 0 ≤ A)
    (hrec : ∀ᶠ n : ℕ in Filter.atTop,
      normalizedEntropy n ≤ A + Real.log (Real.log (Real.log (n : ℝ))) *
        runningMaximum normalizedEntropy (logIndex n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, logS n ≤ C * scale n := by
  have hdecrease : ∀ᶠ n : ℕ in Filter.atTop, logIndex n < n :=
    eventually_log_scale_conditions.mono (fun _ hn => hn.2.2.2.1)
  have hcoeff : ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ Real.log (Real.log (Real.log (n : ℝ))) :=
    eventually_log_scale_conditions.mono (fun _ hn => hn.2.2.2.2.2)
  have hweight : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (Real.log (Real.log (n : ℝ))) * logarithmicWeight (logIndex n) ≤
        logarithmicWeight n := by
    simpa only [logarithmicWeight] using eventually_full_product_step
  obtain ⟨C, hC, hbound⟩ := upper_bound_of_eventual_envelope_recurrence
    normalizedEntropy logarithmicWeight
    (fun n => Real.log (Real.log (Real.log (n : ℝ)))) logIndex A hA
    logarithmicWeight_one_le logarithmicWeight_monotone hdecrease hcoeff hweight hrec
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn₀ : (0 : ℝ) < n := by linarith
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have hfactor : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := div_nonneg hn₀.le hl.le
  have hcancel : ((n : ℝ) / Real.log (n : ℝ)) * normalizedEntropy n = logS n := by
    dsimp [normalizedEntropy]
    field_simp
  calc
    logS n = ((n : ℝ) / Real.log (n : ℝ)) * normalizedEntropy n := hcancel.symm
    _ ≤ ((n : ℝ) / Real.log (n : ℝ)) * (C * logarithmicWeight n) :=
      mul_le_mul_of_nonneg_left (hbound n) hfactor
    _ = C * scale n := by
      dsimp [scale, logarithmicWeight]
      ring

end Erdos320
