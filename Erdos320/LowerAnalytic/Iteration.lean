import Erdos320.LowerAnalytic.Mesh

namespace Erdos320.LowerAnalytic

theorem argument_le_succ (N : ℕ) : argument N ≤ (N + 1 : ℕ) := by
  cases N with
  | zero => norm_num [argument, meshCoordinate]
  | succ N =>
      exact loglog_le_nat (show 2 ≤ N + 1 + 1 by omega)

theorem two_le_of_argument {H : ℝ} (hH : 16 ≤ H) {N : ℕ}
    (hN : H ≤ argument N) : 2 ≤ N := by
  have h := hN.trans (argument_le_succ N)
  by_contra hn
  have hnR : (N : ℝ) ≤ 1 := by exact_mod_cast (show N ≤ 1 by omega)
  push_cast at h
  linarith

theorem logFactors_succ_shift (k : ℕ) (x : ℝ) :
    logFactors (k + 1) x = Real.log x * logFactors k (Real.log x) := by
  unfold logFactors
  rw [Finset.prod_range_succ']
  have hprod : (∏ j ∈ Finset.range k, iterLog (j + 1 + 1) x) =
      ∏ j ∈ Finset.range k, iterLog (j + 1) (Real.log x) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact iterLog_shift (j + 1) x
  rw [hprod]
  change _ * Real.log x = Real.log x * _
  exact mul_comm _ _

/-- An unconditional-in-depth consequence of an explicitly stated renewal
inequality, a prime baseline, and a cofactor endpoint estimate. The actual
counting function must supply those hypotheses separately. -/
theorem depth_lower_bound
    (A : ℕ → ℝ) (y : ℕ → ℕ) (H c₀ : ℝ)
    (hH : 16 ≤ H) (hlogH : 4096 ≤ Real.log H) (hc₀ : 0 < c₀)
    (hbase : ∀ N : ℕ, H ≤ argument N → c₀ * prefactor N ≤ A N)
    (hrec : ∀ N : ℕ, H ≤ argument N → ∀ M : ℕ, 3 ≤ M → M ≤ y N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N)
    (hy : ∀ N : ℕ, H ≤ argument N →
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N)) :
    ∀ k N : ℕ, cutoff H k ≤ argument N →
      c₀ * coefficient k * prefactor N * logFactors k (argument N) ≤ A N := by
  have hH1 : 1 ≤ H := by linarith
  have hHexp : Real.exp 2 ≤ H := by
    have h := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ Real.log H by linarith)
    simpa [Real.exp_log (show 0 < H by linarith)] using h
  intro k
  induction k with
  | zero =>
      intro N hN
      simpa [coefficient_zero, logFactors, cutoff] using hbase N hN
  | succ k ih =>
      intro N hN
      let z : ℝ := argument N
      let L : ℝ := Real.log z
      let a : ℝ := 1 - epsilon k
      let t : ℝ := L ^ a
      let M : ℕ := startingPoint t
      let T : ℝ := ∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))
      have hbaseN : H ≤ argument N := (cutoff_ge_base hH1 (k + 1)).trans hN
      have hN2 : 2 ≤ N := two_le_of_argument hH hbaseN
      have hpref : 0 < prefactor N := by
        unfold prefactor
        exact div_pos (by positivity) (Real.log_pos (by
          exact_mod_cast (show 1 < N by omega)))
      have hzpos : 0 < z := lt_of_lt_of_le (cutoff_pos hH1 (k + 1)) hN
      have hlogz : cutoff H k ^ 2 ≤ L := by
        have h := Real.log_le_log (Real.exp_pos (cutoff H k ^ 2)) hN
        simpa only [cutoff, Real.log_exp] using h
      have hAk : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
      have hAL : cutoff H k ≤ L := by nlinarith
      have hL : 0 < L := lt_of_lt_of_le (cutoff_pos hH1 k) hAL
      have he := epsilon_le k
      have he0 := (epsilon_pos k).le
      have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
      have ha₁ : a ≤ 1 := by dsimp [a]; linarith
      have ha0 : 0 ≤ a := by linarith
      have hAt : cutoff H k ≤ t := cutoff_le_power hH k hlogz
      have ht16 : 16 ≤ t := hAk.trans hAt
      have htSmall : t ≤ epsilon k * L := power_le_epsilon_mul hH hlogH k hAL
      have htpos : 0 < t := Real.rpow_pos_of_pos hL _
      have hE := two_le_epsilon_mul hH hlogH k hAL
      have hyN := hy N hbaseN
      have hend : (1 - epsilon k) * L ≤ meshCoordinate (y N) := by
        dsimp [L, z] at *
        nlinarith [hyN.2]
      have htEnd : t ≤ meshCoordinate (y N) := by nlinarith
      have hM : 3 ≤ M := startingPoint_ge_three ht16
      have hMy : M ≤ y N := startingPoint_le_of_endpoint hyN.1 htEnd
      have hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j L := by
        intro j hj hjk
        exact hHexp.trans (iterLog_ge_base_of_cutoff hH1 k L hAL j hjk)
      have hQ0 := logFactors_nonneg_of_logs hlogs
      have hleft : ∀ m ∈ Finset.Ico M (y N), t ≤ argument m := by
        intro m hm
        exact argument_ge_of_startingPoint (Finset.mem_Ico.mp hm).1
      have hAm : ∀ m ∈ Finset.Ico M (y N),
          (c₀ * coefficient k) * prefactor m * logFactors k (argument m) ≤ A m := by
        intro m hm
        exact ih m (hAt.trans (hleft m hm))
      have hc : 0 ≤ c₀ * coefficient k := mul_nonneg hc₀.le (coefficient_pos k).le
      have hmesh := weighted_mesh_lower A M (y N) k (c₀ * coefficient k) L a
        hM hMy hc hL ha ha₁ hlogs hleft hAm
      have hwidth : (1 - 2 * epsilon k) * L ≤
          meshCoordinate (y N) - meshCoordinate M := by
        have hstart := mesh_startingPoint_le ht16
        change meshCoordinate M ≤ t at hstart
        nlinarith
      have hconst0 : 0 ≤ (c₀ * coefficient k) * a ^ k * logFactors k L := by positivity
      have hsum : c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L *
          logFactors k L ≤ T := by
        calc
          _ = ((c₀ * coefficient k) * a ^ k * logFactors k L) *
              ((1 - 2 * epsilon k) * L) := by ring
          _ ≤ ((c₀ * coefficient k) * a ^ k * logFactors k L) *
              (meshCoordinate (y N) - meshCoordinate M) :=
            mul_le_mul_of_nonneg_left hwidth hconst0
          _ ≤ T := hmesh
      have hsumBase0 : 0 ≤ c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L *
          logFactors k L := by
        have he2 : 0 ≤ 1 - 2 * epsilon k := by linarith
        positivity
      have hT0 : 0 ≤ T := hsumBase0.trans hsum
      have hz1 : 1 ≤ z := le_trans (by norm_num) (hH.trans hbaseN)
      have hlogle := Real.log_le_sub_one_of_pos hzpos
      have hez : 2 ≤ epsilon k * z := by
        dsimp [L] at hE
        nlinarith [mul_le_mul_of_nonneg_left hlogle he0]
      have hezsq : 1 ≤ epsilon k * z ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ z - 1 by linarith)
          (show 0 ≤ epsilon k * z by positivity)]
      have hrecFactor : 1 - epsilon k ≤ 1 - 1 / z ^ 2 := by
        have hdiv : 1 / z ^ 2 ≤ epsilon k := (div_le_iff₀ (sq_pos_of_pos hzpos)).mpr hezsq
        linarith
      have hrecur := hrec N hbaseN M hM hMy
      have hmain : (1 - epsilon k) * prefactor N *
          (c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L * logFactors k L) ≤ A N := by
        calc
          _ ≤ (1 - epsilon k) * prefactor N * T :=
            mul_le_mul_of_nonneg_left hsum (by have := hpref.le; nlinarith)
          _ ≤ (1 - 1 / z ^ 2) * prefactor N * T := by
            have h := mul_le_mul_of_nonneg_right hrecFactor (mul_nonneg hpref.le hT0)
            simpa [mul_assoc] using h
          _ ≤ A N := hrecur
      have hcommon0 : 0 ≤ c₀ * coefficient k * prefactor N * L * logFactors k L := by positivity
      calc
        c₀ * coefficient (k + 1) * prefactor N * logFactors (k + 1) (argument N) =
            (c₀ * coefficient k * prefactor N * L * logFactors k L) *
              (1 - iterationLoss k) := by
          rw [coefficient_succ, logFactors_succ_shift]
          dsimp [L, z]
          ring
        _ ≤ (c₀ * coefficient k * prefactor N * L * logFactors k L) *
            ((1 - epsilon k) * (1 - 2 * epsilon k) * (1 - epsilon k) ^ k) :=
          mul_le_mul_of_nonneg_left (analytic_step_factor_lower k) hcommon0
        _ = (1 - epsilon k) * prefactor N *
            (c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L * logFactors k L) := by
          dsimp [a]
          ring
        _ ≤ A N := hmain

end Erdos320.LowerAnalytic
