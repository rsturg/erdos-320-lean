import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Original analytic scaffolding for Erdős Problem 320.

The theorems here prove an abstract recurrence implication. They do not assume
the desired asymptotic bound, and they do not assert that the prime-block
recurrence has yet been converted to their hypotheses.

The `-A` in the induction invariant is essential: it absorbs the additive
recurrence cost without introducing a fixed multiplicative loss at each
iteration. A product that dominates the exact recurrence coefficients then
controls all iteration depths with one constant.
-/

namespace Erdos320

/-- A nonnegative running maximum, including the value at zero. -/
noncomputable def runningMaximum (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => max 0 (f 0)
  | n + 1 => max (runningMaximum f n) (f (n + 1))

theorem runningMaximum_monotone (f : ℕ → ℝ) : Monotone (runningMaximum f) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem runningMaximum_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ runningMaximum f n := by
  have h₀ : 0 ≤ runningMaximum f 0 := le_max_left _ _
  exact h₀.trans (runningMaximum_monotone f (Nat.zero_le n))

theorem le_runningMaximum (f : ℕ → ℝ) (n : ℕ) : f n ≤ runningMaximum f n := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact le_max_right _ _

theorem le_runningMaximum_of_le (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    f m ≤ runningMaximum f n :=
  (le_runningMaximum f m).trans (runningMaximum_monotone f hmn)

theorem runningMaximum_le (f : ℕ → ℝ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n ≤ N, f n ≤ C) : runningMaximum f N ≤ C := by
  induction N with
  | zero => exact max_le hC (hf 0 le_rfl)
  | succ N ih =>
      apply max_le
      · exact ih (fun n hn => hf n (hn.trans (Nat.le_succ N)))
      · exact hf (N + 1) le_rfl

/-- A finite family of real values admits a positive uniform upper bound. -/
theorem finite_initial_segment_upper_bound (f : ℕ → ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n < N, f n ≤ C := by
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, |f i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, |f i| := by positivity
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n hn
  have hs : |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hn)
  have hf : f n ≤ |f n| := le_abs_self (f n)
  dsimp [C]
  linarith

/-- Solve a recursive upper bound using a product supersolution. The number of
recursive steps is unrestricted. The conclusion is uniform over every input.

The lower bound `2 ≤ b n` supplies enough slack to absorb the fixed additive
cost. It is not a multiplicative approximation to the coefficient: `b n` is
the actual coefficient appearing in `hrec` and `hweight`.
-/
theorem upper_bound_of_contracting_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ) (N₀ : ℕ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hdecrease : ∀ n, N₀ ≤ n → q n < n)
    (hcoeff : ∀ n, N₀ ≤ n → 2 ≤ b n)
    (hweight : ∀ n, N₀ ≤ n → b n * weight (q n) ≤ weight n)
    (hrec : ∀ n, N₀ ≤ n → f n ≤ A + b n * f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨C₀, hC₀, hbase⟩ := finite_initial_segment_upper_bound f N₀
  let C : ℝ := C₀ + A
  have hC : 0 < C := by dsimp [C]; linarith
  have hinvariant : ∀ n, f n ≤ C * weight n - A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < N₀
      · have hfn := hbase n hn
        have hwn := hweight_one n
        have hmul : C₀ + A ≤ (C₀ + A) * weight n := by
          nlinarith
        dsimp [C]
        linarith
      · have hn₀ : N₀ ≤ n := Nat.le_of_not_gt hn
        have hi := ih (q n) (hdecrease n hn₀)
        have hb := hcoeff n hn₀
        have hw := hweight n hn₀
        have hr := hrec n hn₀
        have hb₀ : 0 ≤ b n := by linarith
        have hmul := mul_le_mul_of_nonneg_left hi hb₀
        have hprod := mul_le_mul_of_nonneg_left hw (le_of_lt hC)
        have hcost : 2 * A ≤ b n * A := by nlinarith
        nlinarith
  refine ⟨C, hC, ?_⟩
  intro n
  have hi := hinvariant n
  linarith

/-- Eventual recurrence and product comparison hypotheses are sufficient: all
finitely many exceptional inputs are absorbed into the same positive constant.
-/
theorem upper_bound_of_eventual_contracting_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hdecrease : ∀ᶠ n in Filter.atTop, q n < n)
    (hcoeff : ∀ᶠ n in Filter.atTop, 2 ≤ b n)
    (hweight : ∀ᶠ n in Filter.atTop, b n * weight (q n) ≤ weight n)
    (hrec : ∀ᶠ n in Filter.atTop, f n ≤ A + b n * f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hdecrease.and (hcoeff.and (hweight.and hrec)))
  exact upper_bound_of_contracting_recurrence f weight b q A N₀ hA hweight_one
    (fun n hn => (hN₀ n hn).1)
    (fun n hn => (hN₀ n hn).2.1)
    (fun n hn => (hN₀ n hn).2.2.1)
    (fun n hn => (hN₀ n hn).2.2.2)

/-- The same induction works directly with a running maximum of the recursive
values. Only the comparison weight needs to be monotone; no monotonicity of
the original normalized counting function is asserted or used. -/
theorem upper_bound_of_envelope_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ) (N₀ : ℕ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hweight_mono : Monotone weight)
    (hdecrease : ∀ n, N₀ ≤ n → q n < n)
    (hcoeff : ∀ n, N₀ ≤ n → 2 ≤ b n)
    (hweight : ∀ n, N₀ ≤ n → b n * weight (q n) ≤ weight n)
    (hrec : ∀ n, N₀ ≤ n → f n ≤ A + b n * runningMaximum f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨C₀, hC₀, hbase⟩ := finite_initial_segment_upper_bound f N₀
  let C : ℝ := C₀ + A
  have hC : 0 < C := by dsimp [C]; linarith
  have hinvariant : ∀ n, f n ≤ C * weight n - A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < N₀
      · have hfn := hbase n hn
        have hwn := hweight_one n
        have hmul : C₀ + A ≤ (C₀ + A) * weight n := by nlinarith
        dsimp [C]
        linarith
      · have hn₀ : N₀ ≤ n := Nat.le_of_not_gt hn
        have hq := hdecrease n hn₀
        have hb := hcoeff n hn₀
        have hw := hweight n hn₀
        have hr := hrec n hn₀
        have hMw : 0 ≤ C * weight (q n) - A := by
          have hw₁ := hweight_one (q n)
          dsimp [C]
          nlinarith
        have hM : runningMaximum f (q n) ≤ C * weight (q n) - A := by
          apply runningMaximum_le f (q n) _ hMw
          intro m hm
          have hf := ih m (hm.trans_lt hq)
          have hw_m := hweight_mono hm
          have hcmp := mul_le_mul_of_nonneg_left hw_m hC.le
          linarith
        have hmul := mul_le_mul_of_nonneg_left hM (by linarith : 0 ≤ b n)
        have hprod := mul_le_mul_of_nonneg_left hw hC.le
        have hcost : 2 * A ≤ b n * A := by nlinarith
        nlinarith
  refine ⟨C, hC, ?_⟩
  intro n
  have hi := hinvariant n
  linarith

theorem upper_bound_of_eventual_envelope_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hweight_mono : Monotone weight)
    (hdecrease : ∀ᶠ n in Filter.atTop, q n < n)
    (hcoeff : ∀ᶠ n in Filter.atTop, 2 ≤ b n)
    (hweight : ∀ᶠ n in Filter.atTop, b n * weight (q n) ≤ weight n)
    (hrec : ∀ᶠ n in Filter.atTop, f n ≤ A + b n * runningMaximum f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hdecrease.and (hcoeff.and (hweight.and hrec)))
  exact upper_bound_of_envelope_recurrence f weight b q A N₀ hA hweight_one hweight_mono
    (fun n hn => (hN₀ n hn).1)
    (fun n hn => (hN₀ n hn).2.1)
    (fun n hn => (hN₀ n hn).2.2.1)
    (fun n hn => (hN₀ n hn).2.2.2)

/-- Lift a pointwise recurrence to its running maximum. Small exceptional inputs
are absorbed additively, and the coefficient is retained exactly.

This isolates the monotonic-envelope step from the number-theoretic estimate.
In the intended application, `q n = ⌊log n⌋` and `b n = log₃ n` above a fixed
threshold. No assertion about either function is assumed outside that range.
-/
theorem runningMaximum_recurrence
    (f b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ) (N₀ : ℕ)
    (hA : 0 ≤ A) (hq : Monotone q)
    (hb_nonneg : ∀ n, N₀ ≤ n → 0 ≤ b n)
    (hb_mono : ∀ m n, N₀ ≤ m → m ≤ n → b m ≤ b n)
    (hrec : ∀ n, N₀ ≤ n →
      f n ≤ A + b n * runningMaximum f (q n)) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, N₀ ≤ n →
      runningMaximum f n ≤ B + b n * runningMaximum f (q n) := by
  obtain ⟨C₀, hC₀, hbase⟩ := finite_initial_segment_upper_bound f N₀
  refine ⟨A + C₀, by linarith, ?_⟩
  intro n hn
  have htail_nonneg : 0 ≤ b n * runningMaximum f (q n) :=
    mul_nonneg (hb_nonneg n hn) (runningMaximum_nonneg f (q n))
  apply runningMaximum_le f n (A + C₀ + b n * runningMaximum f (q n))
  · linarith
  intro m hmn
  by_cases hm : m < N₀
  · have hfm := hbase m hm
    linarith
  · have hm₀ : N₀ ≤ m := Nat.le_of_not_gt hm
    have hfm := hrec m hm₀
    have hM : runningMaximum f (q m) ≤ runningMaximum f (q n) :=
      runningMaximum_monotone f (hq hmn)
    have hmul : b m * runningMaximum f (q m) ≤
        b n * runningMaximum f (q n) :=
      mul_le_mul (hb_mono m n hm₀ hmn) hM
        (runningMaximum_nonneg f (q m)) (hb_nonneg n hn)
    linarith

end Erdos320
