import Lax825748.AnalyticChanges
import Lax825748Proofs.Reciprocal
import Lax208278Proofs.CDAAlgebra

noncomputable section

namespace Lax825748Proofs.InverseFrame

open Lax208278.FormalSeries Lax208278.CoordinateChange Lax208278.Monomials
open Lax825748.ConvergentSeries
open Lax208278Proofs ContinuousDerivations
open scoped BigOperators Matrix

theorem constant_polynomial {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ (MvPowerSeries.X i)) = 0)
    (p : MvPolynomial (Fin d) ℝ) :
    MvPowerSeries.constantCoeff (φ p.toMvPowerSeries) = MvPowerSeries.constantCoeff p.toMvPowerSeries := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.coe_C, show φ (MvPowerSeries.C a) = MvPowerSeries.C a from φ.commutes a]
    rfl
  | add p q hp hq => simp only [MvPolynomial.coe_add, map_add, hp, hq]
  | mul_X p i hp => simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, h0,
      MvPowerSeries.constantCoeff_X, mul_zero]

theorem constant_preserving {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    (hc : FormallyContinuous φ)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ (MvPowerSeries.X i)) = 0)
    (f : StateSeries d) : MvPowerSeries.constantCoeff (φ f) = MvPowerSeries.constantCoeff f := by
  obtain ⟨m, hm⟩ := hc 1
  let p := MvPowerSeries.truncTotal (max m 1) f
  have he := hm f p.toMvPowerSeries (trunc_agree f (le_max_left _ _)) 0
    (by simp [totalDegree])
  have hp := trunc_agree f (le_max_right m 1) 0 (by simp [totalDegree])
  exact he.trans ((constant_polynomial φ h0 p).trans hp.symm)

def conjugate {d : ℕ} (φ : FormalChange d) (i : Fin d) :
    Derivation ℝ (StateSeries d) (StateSeries d) where
  toFun f := φ.toAlgEquiv (MvPowerSeries.pderiv ℝ i (φ.toAlgEquiv.symm f))
  map_add' f g := by simp
  map_smul' a f := by simp
  map_one_eq_zero' := by simp
  leibniz' f g := by
    change φ.toAlgEquiv (MvPowerSeries.pderiv ℝ i (φ.toAlgEquiv.symm (f * g))) =
      f * φ.toAlgEquiv (MvPowerSeries.pderiv ℝ i (φ.toAlgEquiv.symm g)) +
      g * φ.toAlgEquiv (MvPowerSeries.pderiv ℝ i (φ.toAlgEquiv.symm f))
    simp only [map_mul, Derivation.leibniz, map_add, smul_eq_mul,
      AlgEquiv.apply_symm_apply]

theorem conjugate_continuous {d : ℕ} (φ : FormalChange d) (i : Fin d) :
    FormallyContinuous (conjugate φ i) := by
  intro n
  obtain ⟨m, hm⟩ := φ.continuous_toFun n
  obtain ⟨k, hk⟩ := φ.continuous_invFun (m + 1)
  refine ⟨k, ?_⟩
  intro f g h
  exact hm _ _ (RepresentationMap.agree_derivative i _ _ (hk f g h))

def frame {d : ℕ} (φ : FormalChange d) : Matrix (Fin d) (Fin d) (StateSeries d) :=
  fun i j => conjugate φ i (MvPowerSeries.X j)

theorem conjugate_field {d : ℕ} (φ : FormalChange d) (i : Fin d) (f : StateSeries d) :
    conjugate φ i f = applyVectorField (frame φ i) f :=
  derivation_eq_field (conjugate φ i) (conjugate_continuous φ i) f

def jacobian {d : ℕ} (φ : FormalChange d) : Matrix (Fin d) (Fin d) (StateSeries d) :=
  fun i j => MvPowerSeries.pderiv ℝ i (φ.toAlgEquiv (MvPowerSeries.X j))

theorem frame_mul_jacobian {d : ℕ} (φ : FormalChange d) : frame φ * jacobian φ = 1 := by
  classical
  apply Matrix.ext
  intro i j
  change applyVectorField (frame φ i) (φ.toAlgEquiv (MvPowerSeries.X j)) = _
  rw [← conjugate_field]
  change φ.toAlgEquiv (MvPowerSeries.pderiv ℝ i
    (φ.toAlgEquiv.symm (φ.toAlgEquiv (MvPowerSeries.X j)))) = _
  rw [AlgEquiv.symm_apply_apply]
  by_cases hij : i = j
  · subst j; simp
  · simp [MvPowerSeries.pderiv_X, hij]

theorem jacobian_det_nonzero {d : ℕ} (φ : FormalChange d) :
    MvPowerSeries.constantCoeff (jacobian φ).det ≠ 0 := by
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) (StateSeries d) =>
    MvPowerSeries.constantCoeff M.det) (frame_mul_jacobian φ)
  rw [Matrix.det_mul, map_mul, Matrix.det_one, map_one] at he
  intro hz
  rw [hz, mul_zero] at he
  exact zero_ne_one he

theorem frame_convergent {d : ℕ} (φ : FormalChange d)
    (hφ : ∀ i, Convergent (φ.toAlgEquiv (MvPowerSeries.X i))) :
    ∀ i j, Convergent (frame φ i j) := by
  obtain ⟨B, hB⟩ := Lax825748.AnalyticCalculus.subalgebra d
  have hJ : ∀ i j, jacobian φ i j ∈ B := fun i j =>
    (hB _).mpr (Lax825748.AnalyticCalculus.partial_derivative _ (hφ j) i)
  have hdet := CDAAlgebra.det_mem B (jacobian φ) hJ
  have hinv : (jacobian φ).det⁻¹ ∈ B := (hB _).mpr
    (Reciprocal.convergent_inverse _ ((hB _).mp hdet) (jacobian_det_nonzero φ))
  have he := congrArg (fun M => M * (jacobian φ).adjugate) (frame_mul_jacobian φ)
  rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
    Matrix.one_mul] at he
  intro i j
  have hij := congrArg (fun M : Matrix (Fin d) (Fin d) (StateSeries d) => M i j) he
  change (jacobian φ).det * frame φ i j = (jacobian φ).adjugate i j at hij
  have hm := B.mul_mem hinv (CDAAlgebra.adjugate_mem B (jacobian φ) hJ i j)
  rw [← hij, ← mul_assoc,
    MvPowerSeries.inv_mul_cancel _ (jacobian_det_nonzero φ), one_mul] at hm
  exact (hB _).mp hm

end Lax825748Proofs.InverseFrame
