import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
Exact statement objects for an independent formalization attempt for
Erdős Problem 320. This file does not assert that an asymptotic bound is proved.

Project commissioned and directed by Riley Sturgill. The user requests project
co-author credit for jenw1n (Jensen Kohlmeyer). No specific mathematical or Lean
contribution by either person is asserted here. Proof development is AI-assisted.

Mathematical sources: Luo, Yang, Zhu, "Distinct Harmonic Subset Sums";
Bettin, Grenié, Molteni, Sanna for the lower bound; Bleicher and Erdős for
the historical prime decomposition and earlier bounds.
-/

namespace Erdos320

/-- Exact rational values of reciprocal subset sums on a denominator set. -/
def sumsOf (A : Finset ℕ) : Finset ℚ :=
  A.powerset.image (fun (B : Finset ℕ) => ∑ n ∈ B, (n : ℚ)⁻¹)

/-- All denominators are positive, and every subset, including empty, is used. -/
def sums (N : ℕ) : Finset ℚ := sumsOf (Finset.Icc 1 N)

/-- Erdős's counting function. -/
def S (N : ℕ) : ℕ := (sums N).card

noncomputable def logS (N : ℕ) : ℝ := Real.log (S N : ℝ)

/-- A finite-height product stopped before logarithmic factors are at most 3.
The final statement uses height `N`; sufficiency of this height must be proved.
-/
noncomputable def stoppedProduct : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x =>
      if x ≤ Real.exp 3 then 1
      else Real.log x * stoppedProduct k (Real.log x)

/-- The full, growing-depth comparison scale. -/
noncomputable def scale (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) *
    stoppedProduct N (Real.log (Real.log N))

/-- The prime blocks in the accepted upper-bound argument. -/
noncomputable def largePrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter
    (fun p => Nat.Prime p ∧ (N : ℝ) / Real.log N < (p : ℝ))

end Erdos320
