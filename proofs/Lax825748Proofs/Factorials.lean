import Lax825748.ConvergenceHypothesis
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

noncomputable section

namespace Lax825748Proofs.Factorials

open Lax825748.Series Lax825748.LieRank Lax825748.Monomials
open Lax825748.ConvergenceHypothesis
open scoped BigOperators

/--
---
conclusion: Lax825748.ConvergenceHypothesis.factorial_comparison
---
The product of factorials divides the total factorial. The multinomial
coefficient is one nonnegative summand in the multinomial expansion of
the power of the number of variables.
-/
theorem factorial_comparison {q : ℕ} (I : Fin q → ℕ) :
    multiFactorial I ≤ (totalDegree I).factorial ∧
      (totalDegree I).factorial ≤ q ^ totalDegree I * multiFactorial I := by
  classical
  refine ⟨Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum _ _), ?_⟩
  have hsum : q ^ totalDegree I =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin q)) (totalDegree I),
        Nat.multinomial Finset.univ k := by
    simpa using Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin q))
      (fun _ => (1 : ℕ)) (totalDegree I)
  have hmem : I ∈ Finset.piAntidiag Finset.univ (totalDegree I) := by
    simp [Finset.mem_piAntidiag, totalDegree]
  have hle : Nat.multinomial Finset.univ I ≤ q ^ totalDegree I := by
    rw [hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  calc
    (totalDegree I).factorial = multiFactorial I * Nat.multinomial Finset.univ I :=
      (Nat.multinomial_spec _ _).symm
    _ ≤ multiFactorial I * q ^ totalDegree I := Nat.mul_le_mul_left _ hle
    _ = _ := Nat.mul_comm _ _

/--
---
conclusion: Lax825748.ConvergenceHypothesis.total_factorial_iff
---
Absorb the exponential factor in the factorial comparison into the
geometric constant. Using $q+1$ also covers the empty family.
-/
theorem total_factorial_iff {X : Type} (g : NCSeries X) :
    Holds g ↔ HoldsWithTotalFactorial g := by
  constructor
  · intro h q P
    obtain ⟨α, hα, C, hC, hb⟩ := h q P
    refine ⟨α, hα, C, hC, fun I => (hb I).trans ?_⟩
    gcongr
    exact_mod_cast (Lax825748.ConvergenceHypothesis.factorial_comparison I).1
  · intro h q P
    obtain ⟨α, hα, C, hC, hb⟩ := h q P
    refine ⟨α, hα, C * (q + 1 : ℕ), by positivity, ?_⟩
    intro I
    have hi : ((totalDegree I).factorial : ℝ) ≤
        (q + 1 : ℕ) ^ totalDegree I * (multiFactorial I : ℝ) := by
      exact_mod_cast ((Lax825748.ConvergenceHypothesis.factorial_comparison I).2.trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ q) _)))
    calc
      _ ≤ α * C ^ totalDegree I * ((totalDegree I).factorial : ℝ) := hb I
      _ ≤ α * C ^ totalDegree I * ((q + 1 : ℕ) ^ totalDegree I * (multiFactorial I : ℝ)) := by
        gcongr
      _ = _ := by rw [mul_pow]; ring

end Lax825748Proofs.Factorials
