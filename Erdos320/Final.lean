import Erdos320.Lower
import Erdos320.UpperAnalyticFinal
import Erdos320.Statement

namespace Erdos320

open Filter

/-- The complete two-sided estimate at the internally convenient threshold 3. -/
theorem two_sided_estimate :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      c * scale N ≤ logS N ∧ logS N ≤ C * scale N := by
  obtain ⟨c, hc, hl⟩ := eventual_lower_bound
  obtain ⟨C, hC, hu⟩ := eventual_upper_bound
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hl, hu] with N hlow hupp
  exact ⟨hlow, hupp⟩

/-- Erdős Problem 320, with the manuscript's exact stopping threshold 2.
`S` counts distinct rational subset sums on `{1,...,N}`. `fullLogProduct`
contains every iterated-log factor strictly above two, and its finite height
is proved sufficient by `fullLogProduct_stable`.
-/
theorem erdos_320 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      c * ((N : ℝ) / Real.log N) * fullLogProduct N ≤ Real.log (S N : ℝ) ∧
      Real.log (S N : ℝ) ≤ C * ((N : ℝ) / Real.log N) * fullLogProduct N := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := two_sided_estimate
  refine ⟨c / 3, C, div_pos hc (by norm_num), hC, ?_⟩
  filter_upwards [hbounds, eventually_ge_atTop (2 : ℕ)] with N hN hlarge
  obtain ⟨hlo, hup⟩ := problemScale_comparison hlarge
  have hlower : (c / 3) * problemScale N ≤ logS N := by
    calc
      _ ≤ (c / 3) * (3 * scale N) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = c * scale N := by ring
      _ ≤ logS N := hN.1
  have hupper : logS N ≤ C * problemScale N :=
    hN.2.trans (mul_le_mul_of_nonneg_left hlo hC.le)
  simpa only [problemScale, logS, mul_assoc] using And.intro hlower hupper

#print axioms erdos_320

end Erdos320
