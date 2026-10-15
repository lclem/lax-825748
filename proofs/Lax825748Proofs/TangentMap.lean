import Lax825748Proofs.ResidualKernel
import Lax825748Proofs.ContinuousDerivations

noncomputable section
namespace Lax825748Proofs.TangentMap

open Lax825748.Series Lax825748.LieRank Lax825748.FormalSeries
open Lax825748.DifferentialRepresentation Lax825748.RepresentationMap
open Rank Operators
open scoped BigOperators

def tangent {X : Type} {d : ℕ} (R : Representation X d) :
    LiePolynomial X →ₗ[ℝ] (Fin d → ℝ) where
  toFun P i := pairing (eta R (MvPowerSeries.X i)) P.val
  map_add' P Q := by funext i; exact Series.pairing_add _ _ _
  map_smul' a P := by funext i; exact Series.pairing_smul _ _ _

theorem pairing_tangent {X : Type} {d : ℕ} (R : Representation X d)
    (P : LiePolynomial X) (f : StateSeries d) :
    pairing (eta R f) P.val =
      ∑ i, tangent R P i * MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℝ i f) := by
  obtain ⟨A, hA⟩ := lie_operator_field R P
  have ht (i : Fin d) : tangent R P i = MvPowerSeries.constantCoeff (A i) := by
    change pairing (eta R (MvPowerSeries.X i)) P.val = _
    rw [pairing_operator, hA, ContinuousDerivations.field_X]
  rw [pairing_operator, hA]
  simp [applyVectorField, ht]

def synthesis {X : Type} {d : ℕ} (R : Representation X d) : (Fin d → ℝ) →ₗ[ℝ] NCSeries X where
  toFun a := ∑ i, a i • tangentSeries R i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum, smul_smul]

theorem residual_factor {X : Type} {d : ℕ} (R : Representation X d) (P : LiePolynomial X) :
    ResidualKernel.residualMap (generatingSeries R) P = synthesis R (tangent R P) := by
  funext w
  change pairing (eta R R.output) (wordPolynomial w * P.val) = _
  rw [← Series.pairing_right_residual, ← Lax825748.RepresentationMap.intertwining R R.output w,
    pairing_tangent]
  simp [synthesis, tangentSeries, Finset.sum_apply]

theorem synthesis_properties {X : Type} {d : ℕ} (R : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) :
    Function.Injective (synthesis R) ∧
      LinearMap.range (synthesis R) = residualSpace (generatingSeries R) := by
  have hle : residualSpace (generatingSeries R) ≤ LinearMap.range (synthesis R) := by
    rw [← ResidualKernel.range_eq]
    rintro T ⟨P, rfl⟩
    exact ⟨tangent R P, (residual_factor R P).symm⟩
  have hdim : Module.finrank ℝ (LinearMap.range (synthesis R)) = d := by
    apply Nat.le_antisymm
    · simpa using LinearMap.finrank_range_le (synthesis R)
    · simpa only [hr.2] using (Submodule.finrank_mono hle)
  have heq : residualSpace (generatingSeries R) = LinearMap.range (synthesis R) :=
    Submodule.eq_of_le_of_finrank_eq hle (hr.2.trans hdim.symm)
  have hinj : Function.Injective (synthesis R) := by
    apply LinearMap.ker_eq_bot.mp
    have hh := (synthesis R).finrank_range_add_finrank_ker
    have hk : Module.finrank ℝ (LinearMap.ker (synthesis R)) = 0 := by
      simp only [Module.finrank_pi, Fintype.card_fin] at hh
      omega
    exact Submodule.finrank_eq_zero.mp hk
  exact ⟨hinj, heq.symm⟩

theorem tangent_surjective {X : Type} {d : ℕ} (R : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) : Function.Surjective (tangent R) := by
  obtain ⟨hi, he⟩ := synthesis_properties R hr
  intro a
  have ha : synthesis R a ∈ residualSpace (generatingSeries R) := by
    rw [← he]; exact ⟨a, rfl⟩
  rw [← ResidualKernel.range_eq] at ha
  obtain ⟨P, hP⟩ := ha
  refine ⟨P, hi ?_⟩
  rw [← residual_factor, hP]

theorem tangent_kernel {X : Type} {d : ℕ} (R : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) (P : LiePolynomial X) :
    tangent R P = 0 ↔ ResidualKernel.residualMap (generatingSeries R) P = 0 := by
  rw [residual_factor]
  exact ((synthesis_properties R hr).1.eq_iff' (map_zero (synthesis R))).symm

end Lax825748Proofs.TangentMap
