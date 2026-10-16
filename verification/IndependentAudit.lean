import Erdos320

namespace IndependentVerification

/-- Literal rational subset-sum count, independent of the project's aliases. -/
def explicitCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.image
    (fun B : Finset ℕ => ∑ n ∈ B, (n : ℚ)⁻¹)).card

example (N : ℕ) : Erdos320.S N = explicitCount N := rfl

example (N : ℕ) : Erdos320.fullLogProduct N =
    Erdos320.stoppedProductAt 2 N (Real.log (Real.log (N : ℝ))) := rfl

/-- This fixed expected type has no implicit or explicit proof hypothesis. -/
theorem expected_erdos_320 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      c * ((N : ℝ) / Real.log N) * Erdos320.fullLogProduct N ≤
          Real.log (explicitCount N : ℝ) ∧
      Real.log (explicitCount N : ℝ) ≤
          C * ((N : ℝ) / Real.log N) * Erdos320.fullLogProduct N :=
  Erdos320.erdos_320

#check @Erdos320.erdos_320
#check @Erdos320.fullLogProduct_stable
#print axioms Erdos320.erdos_320
#print axioms Erdos320.fullLogProduct_stable
#print axioms IndependentVerification.expected_erdos_320

end IndependentVerification
