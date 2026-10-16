import Erdos320.LowerAnalytic.Comparison
import Erdos320.LogScale

namespace Erdos320.LowerAnalytic

/-- A uniform lower renewal and a prime baseline imply the complete growing-
depth stopped-product lower bound. Every analytic hypothesis is explicit. -/
theorem eventual_lower_from_renewal
    (A : ℕ → ℝ) (y : ℕ → ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hbase : ∀ᶠ N : ℕ in Filter.atTop, c₀ * prefactor N ≤ A N)
    (hrec : ∀ᶠ N : ℕ in Filter.atTop, ∀ M : ℕ, 3 ≤ M → M ≤ y N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N)
    (hy : ∀ᶠ N : ℕ in Filter.atTop,
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop, c * scale N ≤ A N := by
  have hdata : ∀ᶠ N : ℕ in Filter.atTop,
      c₀ * prefactor N ≤ A N ∧
      (∀ M : ℕ, 3 ≤ M → M ≤ y N →
        (1 - 1 / argument N ^ 2) * prefactor N *
          (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N) ∧
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N) := by
    filter_upwards [hbase, hrec, hy] with N hb hr hyN
    exact ⟨hb, hr, hyN⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hdata
  let H : ℝ := max (Real.exp 4096) ((N₀ : ℝ) + 16)
  have hH16 : 16 ≤ H := by
    have hmax : (N₀ : ℝ) + 16 ≤ H := le_max_right _ _
    have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    linarith
  have hlogH : 4096 ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos 4096) (le_max_left (Real.exp 4096) ((N₀ : ℝ) + 16))
    simpa [H] using h
  have hlarge : ∀ N : ℕ, H ≤ argument N → N₀ ≤ N := by
    intro N hN
    have hmax : (N₀ : ℝ) + 16 ≤ H := le_max_right _ _
    have harg := argument_le_succ N
    have hreal : (N₀ : ℝ) ≤ N := by
      push_cast at harg
      linarith
    exact_mod_cast hreal
  have hbaseAll : ∀ N : ℕ, H ≤ argument N → c₀ * prefactor N ≤ A N :=
    fun N hN => (hN₀ N (hlarge N hN)).1
  have hrecAll : ∀ N : ℕ, H ≤ argument N → ∀ M : ℕ, 3 ≤ M → M ≤ y N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N :=
    fun N hN => (hN₀ N (hlarge N hN)).2.1
  have hyAll : ∀ N : ℕ, H ≤ argument N →
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N) :=
    fun N hN => (hN₀ N (hlarge N hN)).2.2
  have hdepth := depth_lower_bound A y H c₀ hH16 hlogH hc₀ hbaseAll hrecAll hyAll
  obtain ⟨C, hC, hcompare⟩ := exists_full_product_comparison hH16 hlogH
  let c : ℝ := (7 * c₀) / (8 * C)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hxevent : ∀ᶠ N : ℕ in Filter.atTop, H ≤ meshCoordinate N := by
    simpa [meshCoordinate] using loglog_nat_tendsto.eventually (Filter.eventually_ge_atTop H)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ), hxevent] with N hN hxH
  let x : ℝ := meshCoordinate N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbasic0 : 0 ≤ (N : ℝ) / Real.log N := div_nonneg hNpos.le hlogN.le
  have hx0 : 0 < x := lt_of_lt_of_le (show 0 < H by linarith) hxH
  have hxz : x ≤ argument N := by
    apply Real.log_le_log hlogN
    exact Real.log_le_log hNpos (by exact_mod_cast Nat.le_succ N)
  obtain ⟨k, hk, hfull⟩ := hcompare x hxH
  have hH1 : 1 ≤ H := by linarith
  have hHexp : Real.exp 2 ≤ H := by
    have h := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ Real.log H by linarith)
    simpa [Real.exp_log (show 0 < H by linarith)] using h
  have hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x := by
    intro j hj hjk
    exact hHexp.trans (iterLog_ge_base_of_cutoff hH1 k x hk j hjk)
  have hQ0 := logFactors_nonneg_of_logs hlogs
  have hQ : logFactors k x ≤ logFactors k (argument N) := by
    have h := logFactors_monotone_above_power hx0 (by norm_num : (1 : ℝ) / 2 ≤ 1)
      (le_refl (1 : ℝ)) hlogs (show x ^ (1 : ℝ) ≤ argument N by simpa using hxz)
    simpa using h
  have hA := hdepth k N (hk.trans hxz)
  have hcoeff0 : 0 ≤ c₀ * coefficient k := mul_nonneg hc₀.le (coefficient_pos k).le
  have hpref0 : 0 ≤ prefactor N := by unfold prefactor; positivity
  have hcoeff : (7 / 8 : ℝ) * c₀ ≤ c₀ * coefficient k := by
    have h := mul_le_mul_of_nonneg_left (coefficient_lower k) hc₀.le
    nlinarith
  have hpref : (N : ℝ) / Real.log N ≤ prefactor N := by
    unfold prefactor
    apply div_le_div_of_nonneg_right _ hlogN.le
    push_cast
    linarith
  have hraw : (7 / 8 : ℝ) * c₀ * ((N : ℝ) / Real.log N) * logFactors k x ≤ A N := by
    calc
      _ ≤ (c₀ * coefficient k) * prefactor N * logFactors k x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hpref hbasic0 hcoeff0) hQ0
      _ ≤ (c₀ * coefficient k) * prefactor N * logFactors k (argument N) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg hcoeff0 hpref0)
      _ ≤ A N := hA
  calc
    c * scale N = c * (((N : ℝ) / Real.log N) * stoppedProduct N x) := rfl
    _ ≤ c * (((N : ℝ) / Real.log N) * (C * logFactors k x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hfull N) hbasic0) hc.le
    _ = (7 / 8 : ℝ) * c₀ * ((N : ℝ) / Real.log N) * logFactors k x := by
      dsimp [c]
      field_simp
    _ ≤ A N := hraw

end Erdos320.LowerAnalytic
