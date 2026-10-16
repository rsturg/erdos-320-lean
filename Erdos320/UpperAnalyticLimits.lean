import Erdos320.UpperAnalyticDecay
import Erdos320.UpperAnalyticKernel
import Erdos320.LogScale
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Order.Field

/-! Original limiting estimates for the uniform prime-block error. -/

namespace Erdos320

noncomputable def renewalLogError (L : ℝ) : ℝ :=
  2 * (Real.log (L + 1) / L) + 128 / L ^ 3

noncomputable def renewalError (N : ℕ) : ℝ := renewalLogError (Real.log (N : ℝ))

theorem tendsto_log_add_one_pow_div (k : ℕ) :
    Filter.Tendsto (fun L : ℝ => Real.log (L + 1) ^ k / L)
      Filter.atTop (nhds 0) := by
  have hadd : Filter.Tendsto (fun L : ℝ => L + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  simpa only [Function.comp_def, one_mul, add_neg_cancel_right] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) k one_ne_zero).comp hadd

theorem renewalLogError_mul_loglog_bound {L : ℝ} (hL : 3 ≤ L) :
    0 ≤ renewalLogError L * Real.log (Real.log L) ∧
      renewalLogError L * Real.log (Real.log L) ≤
        130 * (Real.log (L + 1) ^ 2 / L) := by
  have hL₀ : 0 < L := by linarith
  have hL₁ : 1 ≤ L := by linarith
  have hlog₁ : 1 < Real.log L := by
    have h := Real.log_lt_log (Real.exp_pos (1 : ℝ))
      (Real.exp_one_lt_three.trans_le hL)
    simpa only [Real.log_exp] using h
  have hlog₀ : 0 ≤ Real.log L := by linarith
  have hlogplus : Real.log L ≤ Real.log (L + 1) :=
    Real.log_le_log hL₀ (by linarith)
  have hu₁ : 1 ≤ Real.log (L + 1) := by linarith
  have hu₀ : 0 ≤ Real.log (L + 1) := by linarith
  have hT₀ : 0 ≤ Real.log (Real.log L) := Real.log_nonneg hlog₁.le
  have hTu : Real.log (Real.log L) ≤ Real.log (L + 1) :=
    (Real.log_le_self hlog₀).trans hlogplus
  have hLcube : L ≤ L ^ 3 := by
    calc
      L = L * 1 := by ring
      _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL₁) hL₀.le
      _ = L ^ 3 := by ring
  have hLu : L ≤ Real.log (L + 1) * L ^ 3 :=
    hLcube.trans (by nlinarith only [mul_le_mul_of_nonneg_right hu₁ (pow_pos hL₀ 3).le])
  have hinv : 1 / L ^ 3 ≤ Real.log (L + 1) / L := by
    apply (div_le_div_iff₀ (pow_pos hL₀ 3) hL₀).mpr
    simpa using hLu
  have herror₀ : 0 ≤ renewalLogError L := by
    dsimp [renewalLogError]
    positivity
  have herror : renewalLogError L ≤ 130 * Real.log (L + 1) / L := by
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 128)
    calc
      renewalLogError L = 2 * (Real.log (L + 1) / L) + 128 * (1 / L ^ 3) := by
        dsimp [renewalLogError]
        ring
      _ ≤ 2 * (Real.log (L + 1) / L) + 128 * (Real.log (L + 1) / L) :=
        add_le_add le_rfl h
      _ = _ := by ring
  refine ⟨mul_nonneg herror₀ hT₀, ?_⟩
  calc
    renewalLogError L * Real.log (Real.log L)
        ≤ renewalLogError L * Real.log (L + 1) :=
      mul_le_mul_of_nonneg_left hTu herror₀
    _ ≤ (130 * Real.log (L + 1) / L) * Real.log (L + 1) :=
      mul_le_mul_of_nonneg_right herror hu₀
    _ = 130 * (Real.log (L + 1) ^ 2 / L) := by ring

theorem tendsto_renewalLogError_mul_loglog :
    Filter.Tendsto (fun L : ℝ => renewalLogError L * Real.log (Real.log L))
      Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto
      (fun L : ℝ => 130 * (Real.log (L + 1) ^ 2 / L))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_log_add_one_pow_div 2).const_mul (130 : ℝ)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with L hL
    exact (renewalLogError_mul_loglog_bound hL).1
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with L hL
    exact (renewalLogError_mul_loglog_bound hL).2

theorem renewalError_mul_logloglog_tendsto :
    Filter.Tendsto
      (fun N : ℕ => renewalError N * Real.log (Real.log (Real.log (N : ℝ))))
      Filter.atTop (nhds 0) := by
  simpa only [renewalError, Function.comp_def] using
    tendsto_renewalLogError_mul_loglog.comp log_nat_tendsto

theorem eventually_renewalError_nonneg :
    ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ renewalError N := by
  filter_upwards [log_nat_tendsto.eventually (Filter.eventually_ge_atTop (3 : ℝ))]
    with N hN
  have hL₀ : 0 < Real.log (N : ℝ) := by linarith
  have hu : 0 ≤ Real.log (Real.log (N : ℝ) + 1) := Real.log_nonneg (by linarith)
  dsimp [renewalError, renewalLogError]
  positivity

theorem eventually_renewalError_kernel_absorbed :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 + renewalError N) *
          (Real.log (Real.log (Real.log (N : ℝ))) - Real.log (Real.log 3)) ≤
        Real.log (Real.log (Real.log (N : ℝ))) :=
  eventual_multiplicative_error_absorbed_by_margin renewalError
    (fun N => Real.log (Real.log (Real.log (N : ℝ))))
    (Real.log (Real.log 3)) loglog_three_pos
    eventually_renewalError_nonneg renewalError_mul_logloglog_tendsto

theorem eventually_renewalError_le_one :
    ∀ᶠ N : ℕ in Filter.atTop, renewalError N ≤ 1 := by
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop,
      renewalError N * Real.log (Real.log (Real.log (N : ℝ))) < 1 :=
    renewalError_mul_logloglog_tendsto.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_renewalError_nonneg,
    eventually_log_scale_conditions] with N hs hδ hN
  nlinarith [hN.2.2.2.2.2]

theorem eventually_logIndex_three :
    ∀ᶠ N : ℕ in Filter.atTop, 3 ≤ logIndex N := by
  filter_upwards [log_nat_tendsto.eventually (Filter.eventually_ge_atTop (3 : ℝ))]
    with N hN
  exact Nat.le_floor hN

theorem eventually_log_add_one_le_half :
    ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧ 0 ≤ Real.log (L + 1) ∧
      Real.log (L + 1) ≤ L / 2 := by
  have hsmall : ∀ᶠ L : ℝ in Filter.atTop, Real.log (L + 1) / L < 1 / 2 := by
    have h := (tendsto_log_add_one_pow_div 1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [pow_one] using h
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hsmall] with L hL hs
  have hL₀ : 0 < L := by linarith
  refine ⟨hL, Real.log_nonneg (by linarith), ?_⟩
  have h := (div_lt_iff₀ hL₀).mp hs
  linarith

theorem tendsto_div_log_add_one_atTop :
    Filter.Tendsto (fun X : ℝ => X / (Real.log X + 1))
      Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun X : ℝ => Real.log X / X)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Filter.Tendsto (fun X : ℝ => (1 : ℝ) / X)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Filter.tendsto_id 1
  have hratio : Filter.Tendsto (fun X : ℝ => (Real.log X + 1) / X)
      Filter.atTop (nhds 0) := by
    simpa only [add_div, add_zero] using hlog.add hinv
  have hpos : ∀ᶠ X : ℝ in Filter.atTop, 0 < (Real.log X + 1) / X := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (by linarith [Real.log_pos hX]) (by linarith)
  have hwithin : Filter.Tendsto (fun X : ℝ => (Real.log X + 1) / X)
      Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hratio, hpos⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hwithin

end Erdos320
