import Erdos320.LowerAnalytic.Cutoffs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

namespace Erdos320.LowerAnalytic

noncomputable def meshCoordinate (m : ℕ) : ℝ := Real.log (Real.log (m : ℝ))

noncomputable def argument (m : ℕ) : ℝ := meshCoordinate (m + 1)

noncomputable def prefactor (m : ℕ) : ℝ := ((m + 1 : ℕ) : ℝ) / Real.log m

/-- A floor gives an upper bound at the left endpoint and a lower bound at
the right endpoint, exactly matching the discrete mesh. -/
noncomputable def startingPoint (x : ℝ) : ℕ := ⌊Real.exp (Real.exp x)⌋₊

theorem startingPoint_ge_three {x : ℝ} (hx : 16 ≤ x) : 3 ≤ startingPoint x := by
  have h₁ := Real.add_one_le_exp x
  have h₂ := Real.add_one_le_exp (Real.exp x)
  apply Nat.le_floor
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem mesh_startingPoint_le {x : ℝ} (hx : 16 ≤ x) :
    meshCoordinate (startingPoint x) ≤ x := by
  have hM : 3 ≤ startingPoint x := startingPoint_ge_three hx
  have hM0 : (0 : ℝ) < startingPoint x := by exact_mod_cast (show 0 < startingPoint x by omega)
  have hlogM : 0 < Real.log (startingPoint x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < startingPoint x by omega))
  have hfloor : (startingPoint x : ℝ) ≤ Real.exp (Real.exp x) :=
    Nat.floor_le (Real.exp_pos _).le
  have hfirst := Real.log_le_log hM0 hfloor
  rw [Real.log_exp] at hfirst
  have hsecond := Real.log_le_log hlogM hfirst
  simpa [meshCoordinate] using hsecond

theorem argument_ge_of_startingPoint {x : ℝ} {m : ℕ}
    (hm : startingPoint x ≤ m) : x ≤ argument m := by
  have hstart : Real.exp (Real.exp x) ≤ ((m + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp (Real.exp x))
    have hcast : (startingPoint x : ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    change Real.exp (Real.exp x) < (startingPoint x : ℝ) + 1 at h
    linarith
  have hfirst := Real.log_le_log (Real.exp_pos (Real.exp x)) hstart
  rw [Real.log_exp] at hfirst
  have hsecond := Real.log_le_log (Real.exp_pos x) hfirst
  simpa [argument, meshCoordinate] using hsecond

theorem startingPoint_le_of_endpoint {x : ℝ} {y : ℕ} (hy : 3 ≤ y)
    (hx : x ≤ meshCoordinate y) : startingPoint x ≤ y := by
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hfirst := Real.exp_le_exp.mpr hx
  rw [meshCoordinate, Real.exp_log hlogy] at hfirst
  have hsecond := Real.exp_le_exp.mpr hfirst
  rw [Real.exp_log (lt_trans zero_lt_one hyR)] at hsecond
  exact Nat.floor_le_of_le hsecond

theorem mesh_increment_le (m : ℕ) (hm : 2 ≤ m) :
    meshCoordinate (m + 1) - meshCoordinate m ≤
      1 / ((m : ℝ) * Real.log m) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (0 : ℝ) < m := lt_trans zero_lt_one hmR
  have hs0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hl0 : 0 < Real.log (m : ℝ) := Real.log_pos hmR
  have hls0 : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
  have hfirst := Real.log_le_sub_one_of_pos (div_pos hs0 hm0)
  rw [Real.log_div hs0.ne' hm0.ne'] at hfirst
  have hident : ((m : ℝ) + 1) / m - 1 = 1 / (m : ℝ) := by
    field_simp
    ring
  rw [hident] at hfirst
  have hsecond := Real.log_le_sub_one_of_pos (div_pos hls0 hl0)
  rw [Real.log_div hls0.ne' hl0.ne'] at hsecond
  have hident₂ : Real.log ((m : ℝ) + 1) / Real.log m - 1 =
      (Real.log ((m : ℝ) + 1) - Real.log m) / Real.log m := by
    field_simp
  rw [hident₂] at hsecond
  calc
    meshCoordinate (m + 1) - meshCoordinate m =
        Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log m) := by
      simp [meshCoordinate]
    _ ≤ (Real.log ((m : ℝ) + 1) - Real.log m) / Real.log m := hsecond
    _ ≤ (1 / (m : ℝ)) / Real.log m := div_le_div_of_nonneg_right hfirst hl0.le
    _ = _ := by ring

theorem reciprocal_log_sum_lower (M y : ℕ) (hM : 2 ≤ M) (hMy : M ≤ y) :
    meshCoordinate y - meshCoordinate M ≤
      ∑ m ∈ Finset.Ico M y, 1 / ((m : ℝ) * Real.log m) := by
  have h := Finset.sum_le_sum (s := Finset.Ico M y) (fun m hm =>
    mesh_increment_le m (hM.trans (Finset.mem_Ico.mp hm).1))
  rwa [Finset.sum_Ico_sub meshCoordinate hMy] at h

theorem logFactors_nonneg_of_logs {k : ℕ} {L : ℝ}
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j L) :
    0 ≤ logFactors k L := by
  unfold logFactors
  apply Finset.prod_nonneg
  intro j hj
  exact (Real.exp_pos 2).le.trans (hlogs (j + 1) (by omega)
    (by have := Finset.mem_range.mp hj; omega))

/-- A lower benchmark on a variable interval gives a constant multiple of
the elementary reciprocal-logarithm mesh. -/
theorem weighted_mesh_lower (A : ℕ → ℝ) (M y k : ℕ) (c L a : ℝ)
    (hM : 3 ≤ M) (hMy : M ≤ y) (hc : 0 ≤ c) (hL : 0 < L)
    (ha : 1 / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j L)
    (hleft : ∀ m ∈ Finset.Ico M y, L ^ a ≤ argument m)
    (hA : ∀ m ∈ Finset.Ico M y,
      c * prefactor m * logFactors k (argument m) ≤ A m) :
    c * a ^ k * logFactors k L * (meshCoordinate y - meshCoordinate M) ≤
      ∑ m ∈ Finset.Ico M y, A m / ((m : ℝ) * (m + 1)) := by
  have ha0 : 0 ≤ a := by linarith
  have hQ0 := logFactors_nonneg_of_logs hlogs
  have hC0 : 0 ≤ c * a ^ k * logFactors k L := by positivity
  have hsum := mul_le_mul_of_nonneg_left
    (reciprocal_log_sum_lower M y (by omega) hMy) hC0
  apply hsum.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hm3 : 3 ≤ m := hM.trans (Finset.mem_Ico.mp hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmLog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hpref0 : 0 ≤ c * prefactor m := by
    unfold prefactor
    positivity
  have hQ := (logFactors_power_lower hL ha ha₁ hlogs).trans
    (logFactors_monotone_above_power hL ha ha₁ hlogs (hleft m hm))
  have hAm : c * prefactor m * (a ^ k * logFactors k L) ≤ A m :=
    (mul_le_mul_of_nonneg_left hQ hpref0).trans (hA m hm)
  have hdiv := div_le_div_of_nonneg_right hAm
    (show 0 ≤ (m : ℝ) * (m + 1) by positivity)
  convert hdiv using 1
  unfold prefactor
  push_cast
  field_simp

end Erdos320.LowerAnalytic
