import Lax825748.FormalMinimality
import Lax825748Proofs.Operators

noncomputable section

namespace Lax825748Proofs.Rank

open Lax825748.Series Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.RepresentationMap Lax825748.LieRank
open RepresentationMap Operators
open scoped BigOperators

theorem pairing_operator {X : Type} {d : ℕ} (R : Representation X d)
    (f : StateSeries d) (P : NCPolynomial X) :
    pairing (eta R f) P = MvPowerSeries.constantCoeff (operator R P f) := by
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    change pairing (eta R f) (wordPolynomial w) =
      MvPowerSeries.constantCoeff (operator R (wordPolynomial w) f)
    rw [Series.pairing_word, operator_word]
    rfl
  | add P Q hP hQ => simp only [Series.pairing_add, map_add, LinearMap.add_apply, hP, hQ]
  | smul a P hP =>
    simp only [Series.pairing_smul, map_smul, LinearMap.smul_apply,
      MvPowerSeries.constantCoeff_smul, hP, smul_eq_mul]

def tangentSeries {X : Type} {d : ℕ} (R : Representation X d)
    (i : Fin d) : NCSeries X :=
  fun w => MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℝ i (act R R.output w))

theorem residual_in_tangent_span {X : Type} {d : ℕ} (R : Representation X d)
    (P : LiePolynomial X) :
    leftResidual P.val (generatingSeries R) ∈ Submodule.span ℝ (Set.range (tangentSeries R)) := by
  obtain ⟨A, hA⟩ := lie_operator_field R P
  have he : leftResidual P.val (generatingSeries R) =
      ∑ i, MvPowerSeries.constantCoeff (A i) • tangentSeries R i := by
    funext w
    change pairing (eta R R.output) (wordPolynomial w * P.val) = _
    rw [← Series.pairing_right_residual, ← RepresentationMap.intertwining R R.output w,
      pairing_operator, hA]
    simp [applyVectorField, tangentSeries, Finset.sum_apply]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/--
---
conclusion: Lax825748.FormalMinimality.rank_bound
---
Every Lie residual is a linear combination of the $d$ tangent-output series
obtained by differentiating the output trajectories at the origin.
-/
theorem rank_bound {X : Type} {e : ℕ} (R : Representation X e) :
    ∃ d, HasLieRank (generatingSeries R) d ∧ d ≤ e := by
  let T := Submodule.span ℝ (Set.range (tangentSeries R))
  have : Module.Finite ℝ T := Module.Finite.span_of_finite ℝ (Set.finite_range _)
  have hle : residualSpace (generatingSeries R) ≤ T := by
    apply Submodule.span_le.mpr
    rintro S ⟨P, rfl⟩
    exact residual_in_tangent_span R P
  have : Module.Finite ℝ (residualSpace (generatingSeries R)) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  refine ⟨Module.finrank ℝ (residualSpace (generatingSeries R)), ⟨inferInstance, rfl⟩, ?_⟩
  calc
    Module.finrank ℝ (residualSpace (generatingSeries R)) ≤ Module.finrank ℝ T :=
      Submodule.finrank_mono hle
    _ ≤ e := by simpa [T, Set.finrank] using (finrank_range_le_card (R := ℝ) (tangentSeries R))

end Lax825748Proofs.Rank
