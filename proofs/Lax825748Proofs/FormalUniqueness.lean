import Lax825748.FormalUniqueness
import Lax825748Proofs.MinimalEta
import Lax825748Proofs.InverseContinuity

noncomputable section
namespace Lax825748Proofs.FormalUniqueness

open Lax825748.Series Lax825748.LieRank Lax825748.FormalSeries
open Lax825748.DifferentialRepresentation Lax825748.RepresentationMap
open Lax825748.CoordinateChange
open MinimalEta EtaSubstitution

variable {X : Type} {d : ℕ}
variable (R R' : Representation X d)
variable (hr : HasLieRank (generatingSeries R) d) (hr' : HasLieRank (generatingSeries R') d)
variable (hg : generatingSeries R = generatingSeries R')

include hr hr' hg in
theorem transfer_exists (f : StateSeries d) : ∃ k : StateSeries d, eta R' k = eta R f := by
  apply (eta_bijection R' hr').2
  rw [← hg]
  exact eta_ann R hr f

def transfer (f : StateSeries d) : StateSeries d :=
  Classical.choose (transfer_exists R R' hr hr' hg f)

theorem transfer_eta (f : StateSeries d) : eta R' (transfer R R' hr hr' hg f) = eta R f :=
  Classical.choose_spec (transfer_exists R R' hr hr' hg f)

def algebraEquiv : StateSeries d ≃ₐ[ℝ] StateSeries d where
  toFun := transfer R R' hr hr' hg
  invFun := transfer R' R hr' hr hg.symm
  left_inv f := by
    apply (eta_bijection R hr).1
    rw [transfer_eta, transfer_eta]
  right_inv f := by
    apply (eta_bijection R' hr').1
    rw [transfer_eta, transfer_eta]
  map_mul' f k := by
    apply (eta_bijection R' hr').1
    rw [transfer_eta, (Lax825748.RepresentationMap.algebra_homomorphism R').2.2,
      transfer_eta, transfer_eta, (Lax825748.RepresentationMap.algebra_homomorphism R).2.2]
  map_add' f k := by
    apply (eta_bijection R' hr').1
    rw [transfer_eta, (Lax825748.RepresentationMap.algebra_homomorphism R').2.1,
      transfer_eta, transfer_eta, (Lax825748.RepresentationMap.algebra_homomorphism R).2.1]
  commutes' a := by
    apply (eta_bijection R' hr').1
    rw [transfer_eta]
    change eta R (MvPowerSeries.C a) = eta R' (MvPowerSeries.C a)
    rw [(Lax825748.RepresentationMap.algebra_homomorphism R).1,
      (Lax825748.RepresentationMap.algebra_homomorphism R').1]

include hr' in
theorem eta_inverse_continuous : ∀ n, ∃ m, ∀ f k : StateSeries d,
    Lax825748.Series.AgreeBelow m (eta R' f) (eta R' k) →
      Lax825748.FormalSeries.AgreeBelow n f k := by
  obtain ⟨P, hP, hS⟩ := normalized_complement R' hr'
  intro n
  obtain ⟨m, hm⟩ := InverseContinuity.substitute_inverse_continuous P (coordinates R') hS.1 hS.2.2 n
  refine ⟨m, ?_⟩
  intro f k h
  rw [eta_eq_substitute, eta_eq_substitute] at h
  exact hm f k h

include hr hr' hg in
theorem transfer_continuous : Lax825748.FormalSeries.FormallyContinuous (transfer R R' hr hr' hg) := by
  intro n
  obtain ⟨m, hm⟩ := eta_inverse_continuous R' hr' n
  obtain ⟨k, hk⟩ := Lax825748.RepresentationMap.continuous R m
  refine ⟨k, ?_⟩
  intro f g h
  apply hm
  rw [transfer_eta, transfer_eta]
  exact hk f g h

include hr hr' hg in
theorem transfer_origin (i : Fin d) :
    MvPowerSeries.constantCoeff (transfer R R' hr hr' hg (MvPowerSeries.X i)) = 0 := by
  have hh := congrArg (fun T : NCSeries X => T 1) (transfer_eta R R' hr hr' hg (MvPowerSeries.X i))
  simpa [eta] using hh

def formalChange : FormalChange d where
  toAlgEquiv := algebraEquiv R R' hr hr' hg
  continuous_toFun := transfer_continuous R R' hr hr' hg
  continuous_invFun := transfer_continuous R' R hr' hr hg.symm
  origin := transfer_origin R R' hr hr' hg
  inverse_origin := transfer_origin R' R hr' hr hg.symm

/--
---
conclusion: Lax825748.FormalUniqueness.minimal_realizations_equivalent
---
In minimal dimension the tangent residual map is onto. Consequently each
representation's series homomorphism is a continuous algebra isomorphism
onto the same residual-kernel annihilator. Compose these isomorphisms.
-/
theorem minimal_realizations_equivalent {X : Type} [Finite X] {d : ℕ}
    (g : NCSeries X) (hr : HasLieRank g d)
    (R R' : Representation X d) (hR : Represents R g) (hR' : Represents R' g) :
    ∃ φ : FormalChange d,
      φ.toAlgEquiv R.output = R'.output ∧
        ∀ (k : StateSeries d) (w : Word X),
          φ.toAlgEquiv (act R k w) = act R' (φ.toAlgEquiv k) w := by
  change generatingSeries R = g at hR
  change generatingSeries R' = g at hR'
  have hrR : HasLieRank (generatingSeries R) d := by simpa only [hR] using hr
  have hrR' : HasLieRank (generatingSeries R') d := by simpa only [hR'] using hr
  let hg := hR.trans hR'.symm
  refine ⟨formalChange R R' hrR hrR' hg, ?_, ?_⟩
  · apply (eta_bijection R' hrR').1
    change eta R' (transfer R R' hrR hrR' hg R.output) = eta R' R'.output
    rw [transfer_eta]
    exact hg
  · intro k w
    apply (eta_bijection R' hrR').1
    change eta R' (transfer R R' hrR hrR' hg (act R k w)) =
      eta R' (act R' (transfer R R' hrR hrR' hg k) w)
    rw [transfer_eta, Lax825748.RepresentationMap.intertwining,
      Lax825748.RepresentationMap.intertwining, transfer_eta]

end Lax825748Proofs.FormalUniqueness
