import Erdos320.LogProduct

/-! The manuscript's exact stopping convention and its formal correspondence. -/

namespace Erdos320

/-- Successive logarithmic factors strictly above `t`, with a finite height. -/
noncomputable def stoppedProductAt (t : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x =>
      if x ≤ Real.exp t then 1
      else Real.log x * stoppedProductAt t k (Real.log x)

theorem stoppedProductAt_small (t : ℝ) (k : ℕ) {x : ℝ} (hx : x ≤ Real.exp t) :
    stoppedProductAt t k x = 1 := by
  cases k <;> simp [stoppedProductAt, hx]

theorem stoppedProductAt_three (k : ℕ) (x : ℝ) :
    stoppedProductAt 3 k x = stoppedProduct k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [stoppedProductAt, stoppedProduct, ih]

theorem stopping_threshold_two_three (k : ℕ) (x : ℝ) :
    stoppedProductAt 3 k x ≤ stoppedProductAt 2 k x ∧
      stoppedProductAt 2 k x ≤ 3 * stoppedProductAt 3 k x := by
  induction k generalizing x with
  | zero => norm_num [stoppedProductAt]
  | succ k ih =>
      have he : Real.exp (2 : ℝ) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
      by_cases hx₂ : x ≤ Real.exp 2
      · have hx₃ := hx₂.trans he
        norm_num [stoppedProductAt, hx₂, hx₃]
      · have hx₀ : 0 < x := lt_trans (Real.exp_pos 2) (lt_of_not_ge hx₂)
        have hl₂ : 2 < Real.log x := by
          have := Real.log_lt_log (Real.exp_pos 2) (lt_of_not_ge hx₂)
          simpa using this
        by_cases hx₃ : x ≤ Real.exp 3
        · have hl₃ : Real.log x ≤ 3 := by
            have := Real.log_le_log hx₀ hx₃
            simpa using this
          have hsmall : Real.log x ≤ Real.exp 2 :=
            hl₃.trans (by have := Real.add_one_le_exp (2 : ℝ); linarith)
          simp only [stoppedProductAt, if_neg hx₂, if_pos hx₃,
            stoppedProductAt_small 2 k hsmall, mul_one, mul_one]
          constructor <;> linarith
        · obtain ⟨hlo, hup⟩ := ih (Real.log x)
          have hl₀ : 0 ≤ Real.log x := by linarith
          simp only [stoppedProductAt, if_neg hx₂, if_neg hx₃]
          refine ⟨mul_le_mul_of_nonneg_left hlo hl₀, ?_⟩
          calc
            _ ≤ Real.log x * (3 * stoppedProductAt 3 k (Real.log x)) :=
              mul_le_mul_of_nonneg_left hup hl₀
            _ = 3 * (Real.log x * stoppedProductAt 3 k (Real.log x)) := by ring

noncomputable def stoppedArgumentAt (t : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x =>
      if x ≤ Real.exp t then x else stoppedArgumentAt t k (Real.log x)

theorem stoppedArgumentAt_small (t : ℝ) (k : ℕ) {x : ℝ} (hx : x ≤ Real.exp t) :
    stoppedArgumentAt t k x = x := by
  cases k <;> simp [stoppedArgumentAt, hx]

theorem stoppedArgumentAt_active (t : ℝ) (k : ℕ) (x : ℝ)
    (hx : Real.exp t < stoppedArgumentAt t k x) : Real.exp t + (k : ℝ) < x := by
  induction k generalizing x with
  | zero => simpa [stoppedArgumentAt] using hx
  | succ k ih =>
      by_cases hsmall : x ≤ Real.exp t
      · rw [stoppedArgumentAt_small t (k + 1) hsmall] at hx
        exact (not_lt_of_ge hsmall hx).elim
      · have hx₀ : 0 < x := lt_trans (Real.exp_pos t) (lt_of_not_ge hsmall)
        have hnext : Real.exp t < stoppedArgumentAt t k (Real.log x) := by
          simpa [stoppedArgumentAt, hsmall] using hx
        have hh := ih _ hnext
        have hdrop := Real.log_le_sub_one_of_pos hx₀
        push_cast
        linarith

theorem stoppedProductAt_stable {t : ℝ} {k : ℕ} {x : ℝ}
    (hx : stoppedArgumentAt t k x ≤ Real.exp t) :
    ∀ l : ℕ, k ≤ l → stoppedProductAt t l x = stoppedProductAt t k x := by
  induction k generalizing x with
  | zero =>
      intro l hl
      have hs : x ≤ Real.exp t := hx
      rw [stoppedProductAt_small t l hs, stoppedProductAt_small t 0 hs]
  | succ k ih =>
      intro l hl
      by_cases hs : x ≤ Real.exp t
      · rw [stoppedProductAt_small t l hs, stoppedProductAt_small t (k + 1) hs]
      · have hnext : stoppedArgumentAt t k (Real.log x) ≤ Real.exp t := by
          simpa [stoppedArgumentAt, hs] using hx
        cases l with
        | zero => omega
        | succ l =>
            simp only [stoppedProductAt, if_neg hs]
            rw [ih hnext l (by omega)]

/-- This is the manuscript's `L₂(N)`: factors `log₃N, log₄N, ...` strictly
above two. The next theorem formally establishes that height `N` is sufficient. -/
noncomputable def fullLogProduct (N : ℕ) : ℝ :=
  stoppedProductAt 2 N (Real.log (Real.log (N : ℝ)))

theorem fullLogProduct_stable {N k : ℕ} (hN : 2 ≤ N) (hNk : N ≤ k) :
    stoppedProductAt 2 k (Real.log (Real.log (N : ℝ))) = fullLogProduct N := by
  have hstop : stoppedArgumentAt 2 N (Real.log (Real.log (N : ℝ))) ≤ Real.exp 2 := by
    by_contra hn
    have hlarge := stoppedArgumentAt_active 2 N _ (lt_of_not_ge hn)
    have hbound := loglog_le_nat hN
    have := Real.exp_pos (2 : ℝ)
    linarith
  exact stoppedProductAt_stable hstop k hNk

noncomputable def problemScale (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) * fullLogProduct N

theorem problemScale_comparison {N : ℕ} (hN : 2 ≤ N) :
    scale N ≤ problemScale N ∧ problemScale N ≤ 3 * scale N := by
  obtain ⟨hlo, hup⟩ := stopping_threshold_two_three N (Real.log (Real.log (N : ℝ)))
  rw [stoppedProductAt_three] at hlo hup
  have hpre : 0 ≤ (N : ℝ) / Real.log N := by
    apply div_nonneg (by positivity)
    exact (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  refine ⟨mul_le_mul_of_nonneg_left hlo hpre, ?_⟩
  calc
    problemScale N ≤ ((N : ℝ) / Real.log N) *
        (3 * stoppedProduct N (Real.log (Real.log (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left hup hpre
    _ = 3 * scale N := by dsimp [scale]; ring

end Erdos320
