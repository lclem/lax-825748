import Lax825748.Uniqueness
import Lax825748Proofs.PowerSeriesBounds
import Lax208278Proofs.Uniqueness

noncomputable section

namespace Lax825748Proofs.Uniqueness

open Lax208278.Series Lax208278.LieRank Lax208278.FormalSeries
open Lax208278.DifferentialRepresentation Lax208278.RepresentationMap Lax208278.Annihilator
open Lax825748.ConvergentSeries Lax825748.AnalyticRepresentations Lax825748.AnalyticChanges
open Lax208278Proofs MinimalEta EtaSubstitution

theorem eta_convergence {X : Type} {d : ℕ} (R : Representation X d) (ha : IsAnalytic R)
    (f : StateSeries d) (hf : Convergent f) : Lax825748.ConvergenceHypothesis.Holds (eta R f) :=
  Lax825748.NecessaryConvergence.convergence {R with output := f} ⟨hf, ha.2⟩

theorem transfer_convergent {X : Type} {d : ℕ} (R R' : Representation X d)
    (hr : HasLieRank (generatingSeries R) d) (hr' : HasLieRank (generatingSeries R') d)
    (hg : generatingSeries R = generatingSeries R') (ha : IsAnalytic R) (ha' : IsAnalytic R')
    (f : StateSeries d) (hf : Convergent f) :
    Convergent (Lax208278Proofs.Uniqueness.transfer R R' hr hr' hg f) := by
  obtain ⟨P, hP, hT⟩ := normalized_complement R' hr'
  have hCT : ∀ i, Lax825748.ConvergenceHypothesis.Holds (coordinates R' i) :=
    fun i => eta_convergence R' ha' _ (PowerSeriesBounds.convergent_X i)
  have hann := eta_ann R hr f
  rw [hg] at hann
  obtain ⟨u, hu, he⟩ := Lax825748.AnalyticCoordinates.expansion_converges
    (ResidualKernel.kernel (generatingSeries R')) P hP (coordinates R') hT hCT
    (eta R f) hann (eta_convergence R ha f hf)
  have heq : Lax208278Proofs.Uniqueness.transfer R R' hr hr' hg f = u := by
    apply (eta_bijection R' hr').1
    rw [Lax208278Proofs.Uniqueness.transfer_eta, eta_eq_substitute R' u, he]
  rw [heq]
  exact hu

/--
---
conclusion: Lax825748.Uniqueness.minimal_realizations_equivalent
---
The formal equivalence identifies the two representation maps onto their
common annihilator. Their coordinate series satisfy (C); the analytic
coordinate theorem makes the equivalence and its inverse convergent.
-/
theorem minimal_realizations_equivalent {X : Type} [Finite X] {d : ℕ}
    (g : NCSeries X) (hr : HasLieRank g d)
    (R R' : Representation X d) (hR : Represents R g) (hR' : Represents R' g)
    (ha : IsAnalytic R) (ha' : IsAnalytic R') :
    ∃ φ : AnalyticChange d,
      φ.toAlgEquiv R.output = R'.output ∧
        ∀ (k : StateSeries d) (w : Word X),
          φ.toAlgEquiv (act R k w) = act R' (φ.toAlgEquiv k) w := by
  change generatingSeries R = g at hR
  change generatingSeries R' = g at hR'
  have hrR : HasLieRank (generatingSeries R) d := by simpa only [hR] using hr
  have hrR' : HasLieRank (generatingSeries R') d := by simpa only [hR'] using hr
  let hg := hR.trans hR'.symm
  let φ : AnalyticChange d :=
    { toFormalChange := Lax208278Proofs.Uniqueness.formalChange R R' hrR hrR' hg
      convergent_toFun := fun i => transfer_convergent R R' hrR hrR' hg ha ha'
        (MvPowerSeries.X i) (PowerSeriesBounds.convergent_X i)
      convergent_invFun := fun i => transfer_convergent R' R hrR' hrR hg.symm ha' ha
        (MvPowerSeries.X i) (PowerSeriesBounds.convergent_X i) }
  refine ⟨φ, ?_, ?_⟩
  · apply (eta_bijection R' hrR').1
    change eta R' (Lax208278Proofs.Uniqueness.transfer R R' hrR hrR' hg R.output) = eta R' R'.output
    rw [Lax208278Proofs.Uniqueness.transfer_eta]
    exact hg
  · intro k w
    apply (eta_bijection R' hrR').1
    change eta R' (Lax208278Proofs.Uniqueness.transfer R R' hrR hrR' hg (act R k w)) =
      eta R' (act R' (Lax208278Proofs.Uniqueness.transfer R R' hrR hrR' hg k) w)
    rw [Lax208278Proofs.Uniqueness.transfer_eta, Lax208278.RepresentationMap.intertwining,
      Lax208278.RepresentationMap.intertwining, Lax208278Proofs.Uniqueness.transfer_eta]

end Lax825748Proofs.Uniqueness
