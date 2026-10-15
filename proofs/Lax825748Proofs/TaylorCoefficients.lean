import Lax825748Proofs.PowerSeriesBounds
import Lax825748Proofs.ContinuousDerivations

noncomputable section

namespace Lax825748Proofs.TaylorCoefficients

open Lax825748.Series Lax825748.FormalSeries Lax825748.Monomials
open Lax825748.DifferentialRepresentation
open scoped BigOperators

def derivativeRepresentation (d : ℕ) : Representation (Fin d) d :=
  ⟨fun i j => if i = j then 1 else 0, 0⟩

theorem derivative_field {d : ℕ} (i : Fin d) (f : StateSeries d) :
    applyVectorField ((derivativeRepresentation d).fields i) f = MvPowerSeries.pderiv ℝ i f := by
  classical
  simp [derivativeRepresentation, applyVectorField]

theorem factorial_add_single {d : ℕ} (J : Fin d →₀ ℕ) (i : Fin d) :
    multiFactorial (J + Finsupp.single i 1 : Fin d →₀ ℕ) = (J i + 1) * multiFactorial J := by
  classical
  calc
    _ = ∏ j, (if j = i then J i + 1 else 1) * (J j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [Nat.factorial_succ]
      · simp [hj]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [multiFactorial]

theorem derivative_word {d : ℕ} (I : Fin d →₀ ℕ) :
    ∃ w : Word (Fin d), w.toList.length = totalDegree I ∧
      ∀ f : StateSeries d, MvPowerSeries.constantCoeff (act (derivativeRepresentation d) f w) =
        (multiFactorial I : ℝ) * MvPowerSeries.coeff I f := by
  classical
  generalize hn : totalDegree I = n
  induction n using Nat.strong_induction_on generalizing I with
  | h n ih =>
    by_cases hz : I = 0
    · subst I
      refine ⟨1, by simpa [totalDegree] using hn, ?_⟩
      intro f
      simp [act, multiFactorial, MvPowerSeries.coeff_zero_eq_constantCoeff]
    · obtain ⟨i, hi⟩ : ∃ i, I i ≠ 0 := by
        by_contra! hh
        exact hz (Finsupp.ext hh)
      let J := I - Finsupp.single i 1
      have he : J + Finsupp.single i 1 = I := by
        apply Finsupp.ext
        intro j
        by_cases hj : j = i
        · subst j
          simp only [J, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [J, hj]
      have hjn : totalDegree J + 1 = n := by
        rw [← hn, ← he, PowerSeriesBounds.degree_add, PowerSeriesBounds.degree_single]
      obtain ⟨w, hw, hf⟩ := ih (totalDegree J) (by omega) J rfl
      refine ⟨FreeMonoid.of i * w, ?_, ?_⟩
      · simpa only [FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_of,
          List.length_singleton, hw, Nat.add_comm] using hjn
      · intro f
        rw [Lax825748Proofs.RepresentationMap.act_cons, derivative_field, hf,
          MvPowerSeries.coeff_pderiv, he]
        have hfac : (multiFactorial I : ℝ) = ((J i : ℝ) + 1) * (multiFactorial J : ℝ) := by
          rw [← he, factorial_add_single]
          norm_cast
        rw [hfac]
        ring

end Lax825748Proofs.TaylorCoefficients
