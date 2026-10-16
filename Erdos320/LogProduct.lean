import Erdos320.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Elementary stopped-logarithm lemmas, developed for this project. -/

namespace Erdos320

private theorem log_gt_three {x : ℝ} (hx : Real.exp 3 < x) :
    3 < Real.log x := by
  have := Real.log_lt_log (Real.exp_pos 3) hx
  simpa using this

theorem stoppedProduct_eq_one {x : ℝ} (hx : x ≤ Real.exp 3) (k : ℕ) :
    stoppedProduct k x = 1 := by
  cases k with
  | zero => rfl
  | succ k => simp [stoppedProduct, hx]

theorem one_le_stoppedProduct (k : ℕ) (x : ℝ) :
    1 ≤ stoppedProduct k x := by
  induction k generalizing x with
  | zero => simp [stoppedProduct]
  | succ k ih =>
      by_cases hx : x ≤ Real.exp 3
      · simp [stoppedProduct, hx]
      · have hlog : 1 ≤ Real.log x := le_of_lt (lt_trans (by norm_num) (log_gt_three (lt_of_not_ge hx)))
        simp only [stoppedProduct, if_neg hx]
        exact one_le_mul_of_one_le_of_one_le hlog (ih _)

theorem stoppedProduct_pos (k : ℕ) (x : ℝ) :
    0 < stoppedProduct k x := lt_of_lt_of_le zero_lt_one (one_le_stoppedProduct k x)

theorem stoppedProduct_mono_height {a b : ℕ} (hab : a ≤ b) (x : ℝ) :
    stoppedProduct a x ≤ stoppedProduct b x := by
  have hstep : ∀ k : ℕ, ∀ y : ℝ, stoppedProduct k y ≤ stoppedProduct (k + 1) y := by
    intro k
    induction k with
    | zero => intro y; simpa [stoppedProduct] using one_le_stoppedProduct 1 y
    | succ k ih =>
        intro y
        by_cases hy : y ≤ Real.exp 3
        · simp [stoppedProduct, hy]
        · simp only [stoppedProduct, if_neg hy]
          exact mul_le_mul_of_nonneg_left (ih _) (le_of_lt (lt_trans (by norm_num) (log_gt_three (lt_of_not_ge hy))))
  exact (monotone_nat_of_le_succ (fun k => hstep k x)) hab

theorem stoppedProduct_monotone (k : ℕ) : Monotone (stoppedProduct k) := by
  induction k with
  | zero => intro x y hxy; simp [stoppedProduct]
  | succ k ih =>
      intro x y hxy
      by_cases hx : x ≤ Real.exp 3
      · rw [stoppedProduct_eq_one hx]
        exact one_le_stoppedProduct _ _
      · have hx' : Real.exp 3 < x := lt_of_not_ge hx
        have hy : ¬y ≤ Real.exp 3 := not_le.mpr (lt_of_lt_of_le hx' hxy)
        have hx0 : 0 < x := lt_trans (Real.exp_pos 3) hx'
        have hlogs : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
        simp only [stoppedProduct, if_neg hx, if_neg hy]
        exact mul_le_mul hlogs (ih hlogs) (le_of_lt (stoppedProduct_pos _ _))
          (le_of_lt (lt_trans (by norm_num) (log_gt_three (lt_of_not_ge hy))))

/-- The stopped logarithmic map fixes every argument at or below the threshold. -/
noncomputable def logStep (x : ℝ) : ℝ :=
  if x ≤ Real.exp 3 then x else Real.log x

noncomputable def logOrbit : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => logOrbit k (logStep x)

theorem logOrbit_of_small {x : ℝ} (hx : x ≤ Real.exp 3) (k : ℕ) :
    logOrbit k x = x := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [logOrbit, logStep, hx] using ih

theorem active_orbit_requires_large_input (k : ℕ) (x : ℝ)
    (hactive : Real.exp 3 < logOrbit k x) :
    Real.exp 3 + (k : ℝ) < x := by
  induction k generalizing x with
  | zero => simpa [logOrbit] using hactive
  | succ k ih =>
      by_cases hx : x ≤ Real.exp 3
      · rw [logOrbit_of_small hx] at hactive
        exact (not_lt_of_ge hx hactive).elim
      · have hx' : Real.exp 3 < x := lt_of_not_ge hx
        have hnext : Real.exp 3 < logOrbit k (Real.log x) := by
          simpa [logOrbit, logStep, hx] using hactive
        have hlarge := ih _ hnext
        have hdrop := Real.log_le_sub_one_of_pos (lt_trans (Real.exp_pos 3) hx')
        push_cast
        linarith

theorem logOrbit_stops {k : ℕ} {x : ℝ}
    (hx : x ≤ Real.exp 3 + (k : ℝ)) :
    logOrbit k x ≤ Real.exp 3 := by
  by_contra hn
  exact (not_lt_of_ge hx) (active_orbit_requires_large_input k x (lt_of_not_ge hn))

theorem stoppedProduct_stable {k : ℕ} {x : ℝ}
    (hstop : logOrbit k x ≤ Real.exp 3) :
    ∀ l : ℕ, k ≤ l → stoppedProduct l x = stoppedProduct k x := by
  induction k generalizing x with
  | zero =>
      intro l hl
      have hx : x ≤ Real.exp 3 := hstop
      simp [stoppedProduct_eq_one hx]
  | succ k ih =>
      intro l hl
      by_cases hx : x ≤ Real.exp 3
      · simp [stoppedProduct_eq_one hx]
      · have hstop' : logOrbit k (Real.log x) ≤ Real.exp 3 := by
          simpa [logOrbit, logStep, hx] using hstop
        cases l with
        | zero => omega
        | succ l =>
            simp only [stoppedProduct, if_neg hx]
            rw [ih hstop' l (by omega)]

theorem stoppedProduct_stable_of_input_le {k : ℕ} {x : ℝ}
    (hx : x ≤ Real.exp 3 + (k : ℝ)) {l : ℕ} (hkl : k ≤ l) :
    stoppedProduct l x = stoppedProduct k x :=
  stoppedProduct_stable (logOrbit_stops hx) l hkl

theorem loglog_le_nat {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log (N : ℝ)) ≤ (N : ℝ) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNR
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hfirst := Real.log_le_sub_one_of_pos hN0
  have hsecond := Real.log_le_sub_one_of_pos hlog
  linarith

theorem stoppedProduct_stable_at_nat {N k : ℕ} (hN : 2 ≤ N) (hNk : N ≤ k) :
    stoppedProduct k (Real.log (Real.log (N : ℝ))) =
      stoppedProduct N (Real.log (Real.log (N : ℝ))) := by
  apply stoppedProduct_stable_of_input_le _ hNk
  have := loglog_le_nat hN
  have := Real.exp_pos (3 : ℝ)
  linarith

/-- The one-step scale comparison at any smaller integer argument. -/
theorem log_factor_product_comparison {n q : ℕ} (hq : 2 ≤ q) (hqn : q < n)
    (harg : Real.log (Real.log (q : ℝ)) ≤
      Real.log (Real.log (Real.log (n : ℝ))))
    (hactive : Real.exp 3 < Real.log (Real.log (n : ℝ))) :
    Real.log (Real.log (Real.log (n : ℝ))) *
        stoppedProduct q (Real.log (Real.log (q : ℝ))) ≤
      stoppedProduct n (Real.log (Real.log (n : ℝ))) := by
  have hqheight : q ≤ n - 1 := by omega
  have hP := stoppedProduct_monotone q harg
  have hH := stoppedProduct_mono_height hqheight
    (Real.log (Real.log (Real.log (n : ℝ))))
  have hlog : 0 ≤ Real.log (Real.log (Real.log (n : ℝ))) :=
    le_of_lt (lt_trans (by norm_num) (log_gt_three hactive))
  have hn : n = (n - 1) + 1 := by omega
  have hrec : stoppedProduct n (Real.log (Real.log (n : ℝ))) =
      Real.log (Real.log (Real.log (n : ℝ))) *
        stoppedProduct (n - 1) (Real.log (Real.log (Real.log (n : ℝ)))) := by
    have hh := congrArg (fun j : ℕ =>
      stoppedProduct j (Real.log (Real.log (n : ℝ)))) hn
    rw [stoppedProduct, if_neg (not_le.mpr hactive)] at hh
    exact hh
  rw [hrec]
  exact mul_le_mul_of_nonneg_left (hP.trans hH) hlog

theorem log_factor_product_of_le_log {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hqn : (q : ℝ) ≤ Real.log (n : ℝ))
    (hactive : Real.exp 3 < Real.log (Real.log (n : ℝ))) :
    Real.log (Real.log (Real.log (n : ℝ))) *
        stoppedProduct q (Real.log (Real.log (q : ℝ))) ≤
      stoppedProduct n (Real.log (Real.log (n : ℝ))) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hsmall := Real.log_le_sub_one_of_pos hn0
  have hqnNat : q < n := by
    have : (q : ℝ) < n := by linarith
    exact_mod_cast this
  apply log_factor_product_comparison hq hqnNat _ hactive
  have hfirst := Real.log_le_log hq0 hqn
  exact Real.log_le_log (Real.log_pos (by linarith)) hfirst

end Erdos320
