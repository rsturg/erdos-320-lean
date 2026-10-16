import Erdos320.LowerAbel
import Erdos320.LowerCofactors
import Erdos320.PrimeCountingEventual
import Erdos320.LowerAnalytic.Mesh

/-!
The actual independent-denominator count satisfies every input to the generic
uniform lower-renewal argument. The prime estimate used here is proved from the
audited quantitative PNT, and the finite counting/Abel steps are exact.
-/

namespace Erdos320

open Filter LowerAnalytic

theorem eventual_independent_prime_baseline :
    ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) * prefactor N ≤ independentCount N := by
  filter_upwards [eventual_uniform_prime_difference,
    eventually_lower_cofactor_conditions, eventually_ge_atTop (2 : ℕ),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (2 : ℝ))]
      with N hprime hy hN hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have harg : 2 ≤ argument N := by
    apply le_trans hz
    apply Real.log_le_log hlogPos
    exact Real.log_le_log hNpos (by exact_mod_cast (Nat.le_succ N))
  have hargPos : 0 < argument N := by linarith
  have hfrac : 1 / argument N ^ 2 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hargPos)).mpr
    nlinarith
  have hpref : 0 ≤ prefactor N := by
    unfold prefactor
    exact div_nonneg (by positivity) hlogPos.le
  have hp := hprime 1 (by norm_num) (by omega)
  have hprime' : (1 - 1 / argument N ^ 2) * prefactor N ≤
      (Nat.primeCounting N : ℝ) - Nat.primeCounting (compatibilityCutoff 1) := by
    simpa only [argument, meshCoordinate, prefactor, Nat.cast_add, Nat.cast_one,
      Nat.div_one, div_one, mul_div_assoc] using hp
  calc
    (1 / 2 : ℝ) * prefactor N ≤
        (1 - 1 / argument N ^ 2) * prefactor N := by
      exact mul_le_mul_of_nonneg_right (by linarith) hpref
    _ ≤ (Nat.primeCounting N : ℝ) :=
      hprime'.trans (sub_le_self _ (by positivity))
    _ ≤ independentCount N := primeCounting_le_independentCount N

theorem eventual_independent_lower_recurrence :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, 3 ≤ M → M ≤ lowerCofactorBound N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (lowerCofactorBound N),
          independentCount m / ((m : ℝ) * (m + 1))) ≤ independentCount N := by
  filter_upwards [eventual_uniform_prime_difference,
    eventually_basic_prime_conditions] with N hprime hsize
  intro M hM hMy
  have hz : 1 ≤ argument N := hsize.2.2.2.2.1
  have hzPos : 0 < argument N := by linarith
  have hfrac : 1 / argument N ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hzPos)).mpr
    nlinarith
  have hlog : 0 ≤ Real.log (N : ℝ) := by linarith [hsize.2.1]
  let a : ℝ := (1 - 1 / argument N ^ 2) * prefactor N
  have ha : 0 ≤ a := by
    dsimp [a, prefactor]
    exact mul_nonneg (by linarith) (div_nonneg (by positivity) hlog)
  have hprime' : ∀ m : ℕ, 1 ≤ m → m ≤ lowerCofactorBound N →
      a / (m : ℝ) ≤ (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (compatibilityCutoff m) := by
    intro m hm hmy
    simpa only [a, argument, meshCoordinate, prefactor, Nat.cast_add, Nat.cast_one,
      mul_div_assoc] using hprime m hm hmy
  exact finite_lower_mesh N (lowerCofactorBound N) M a ha (by omega) hprime'

theorem eventual_independent_lower_endpoint :
    ∀ᶠ N : ℕ in atTop,
      3 ≤ lowerCofactorBound N ∧
        Real.log (argument N) - 2 ≤ meshCoordinate (lowerCofactorBound N) := by
  filter_upwards [eventually_lower_cofactor_conditions] with N hN
  exact ⟨hN.1, hN.2.2⟩

end Erdos320
