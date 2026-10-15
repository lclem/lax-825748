import Lax825748Proofs.TangentMap
import Lax825748Proofs.EtaSubstitution

noncomputable section
namespace Lax825748Proofs.MinimalEta

open Lax825748.Series Lax825748.LieRank Lax825748.FormalSeries
open Lax825748.DifferentialRepresentation Lax825748.RepresentationMap Lax825748.Annihilator
open TangentMap ResidualKernel EtaSubstitution
open scoped BigOperators

theorem eta_ann {X : Type} {d : ℕ} (R : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) (f : StateSeries d) :
    InAnnihilator (kernel (generatingSeries R)) (eta R f) := by
  intro Q hQ
  have hall : ∀ Q ∈ generatedIdeal (kernel (generatingSeries R)), ∀ A : NCPolynomial X,
      pairing (eta R f) (A * Q) = 0 := by
    intro Q hQ
    change Q ∈ Submodule.span (NCPolynomial X)
      {Q | ∃ k : kernel (generatingSeries R), Q = k.val.val} at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨k, rfl⟩ := hQ
      intro A
      have ht : tangent R k.val = 0 := (tangent_kernel R hr k.val).mpr k.property
      induction A using MonoidAlgebra.induction_on with
      | of w =>
        change pairing (eta R f) (wordPolynomial w * k.val.val) = 0
        rw [← Series.pairing_right_residual, ← Lax825748.RepresentationMap.intertwining R f w,
          pairing_tangent, ht]
        simp
      | add A B hA hB => simp [add_mul, hA, hB]
      | smul a A hA => simp [hA]
    | zero => intro A; simp
    | add Q T _ _ hQ hT => intro A; simp [mul_add, hQ, hT]
    | smul B Q _ hQ =>
      intro A
      change pairing (eta R f) (A * (B * Q)) = 0
      rw [← mul_assoc]
      exact hQ (A * B)
  simpa only [one_mul] using hall Q hQ 1

theorem normalized_complement {X : Type} {d : ℕ} (R : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) :
    ∃ P : Fin d → LiePolynomial X,
      IsComplement (kernel (generatingSeries R)) P ∧
      IsCoordinateFamily (kernel (generatingSeries R)) P (coordinates R) := by
  classical
  let K := kernel (generatingSeries R)
  let eqv := (tangent R).quotKerEquivOfSurjective (tangent_surjective R hr)
  let b := (Pi.basisFun ℝ (Fin d)).map eqv.symm
  choose P hP using fun i : Fin d => (LinearMap.ker (tangent R)).mkQ_surjective (b i)
  have hk : LinearMap.ker (tangent R) = K.toSubmodule := by
    ext P
    exact tangent_kernel R hr P
  have ht (i : Fin d) : tangent R (P i) = Pi.single i 1 := by
    have hh := congrArg eqv (hP i)
    simpa [eqv, b] using hh
  refine ⟨P, ⟨?_, ?_⟩, coordinates_zero R, fun i => eta_ann R hr _, ?_⟩
  · rw [← hk]
    simpa only [hP] using b.linearIndependent
  · rw [← hk]
    simpa only [hP] using b.span_eq
  · intro i j
    have hh := congrFun (ht j) i
    simpa only [tangent, LinearMap.coe_mk, AddHom.coe_mk, coordinates, Pi.single_apply,
      eq_comm] using hh

theorem eta_bijection {X : Type} {d : ℕ} (R : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) :
    Function.Injective (eta R) ∧
      ∀ T : NCSeries X, InAnnihilator (kernel (generatingSeries R)) T → ∃ f, eta R f = T := by
  obtain ⟨P, hP, hS⟩ := normalized_complement R hr
  constructor
  · intro f g hfg
    have hf := eta_ann R hr f
    obtain ⟨k, hk, hu⟩ := (Lax825748.Annihilator.formal_coordinates _ P hP _ hS (eta R f)).mp hf
    have hfs : substituteShuffle (coordinates R) f = eta R f := (eta_eq_substitute R f).symm
    have hgs : substituteShuffle (coordinates R) g = eta R f := by rw [← eta_eq_substitute, hfg]
    exact (hu f hfs).trans (hu g hgs).symm
  · intro T hT
    obtain ⟨f, hf, _⟩ := (Lax825748.Annihilator.formal_coordinates _ P hP _ hS T).mp hT
    exact ⟨f, (eta_eq_substitute R f).trans hf⟩

end Lax825748Proofs.MinimalEta
