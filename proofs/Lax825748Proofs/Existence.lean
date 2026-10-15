import Lax825748.Realization
import Lax825748Proofs.GeneralCoordinates
import Lax825748Proofs.ResidualCoordinates

noncomputable section

namespace Lax825748Proofs.Existence

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries Lax825748.DifferentialRepresentation Lax825748.RepresentationMap
open Lax825748.ConvergentSeries Lax825748.AnalyticRepresentations
open Lax825748Proofs

/--
---
conclusion: Lax825748.Realization.existence
---
Use normalized, centered polynomial residuals as coordinates on the
residual-kernel annihilator. Both the output and the letter residuals of
the coordinates satisfy (C), so their coordinate expressions converge.
-/
theorem existence {X : Type} [Finite X] (g : NCSeries X) (d : ℕ)
    (hr : HasLieRank g d) (hC : Lax825748.ConvergenceHypothesis.Holds g) :
    ∃ R : Representation X d, IsAnalytic R ∧ Represents R g := by
  let K := ResidualKernel.kernel g
  obtain ⟨P, hP⟩ := ResidualKernel.complement_exists g d hr
  have hK : ∀ L : LiePolynomial X, L ∈ K ↔ leftResidual L.val g = 0 := fun _ => Iff.rfl
  obtain ⟨Q, hQ⟩ := ResidualCoordinates.dual_polynomials g K hK P hP
  let T := ResidualCoordinates.coordinates g Q
  have hT : IsCoordinateFamily K P T :=
    ResidualCoordinates.coordinates_family g K hK P Q hQ
  have hCT : ∀ i, Lax825748.ConvergenceHypothesis.Holds (T i) :=
    fun i => Lax825748.ResidualConvergence.centered_residual g hC (Q i)
  obtain ⟨u, hu, he⟩ := Lax825748.AnalyticCoordinates.expansion_converges
    K P hP T hT hCT g (ResidualKernel.series_ann g) hC
  let R := GeneralCoordinates.representation K P hP T hT u
  refine ⟨R, ⟨hu, ?_⟩, ?_⟩
  · intro x i
    have hann := Lax825748.Annihilator.closed_residual K (T i) (hT.2.1 i) (letter x)
    have hconv := Lax825748.ResidualConvergence.right_residual (T i) (hCT i) (letter x)
    obtain ⟨f, hf, hfe⟩ := Lax825748.AnalyticCoordinates.expansion_converges
      K P hP T hT hCT (rightResidual (T i) (letter x)) hann hconv
    have hop : R.fields x i = f := by
      apply GeneralCoordinates.substitute_injective K P hP T hT
      change substituteShuffle T (GeneralCoordinates.operator K P hP T hT x (MvPowerSeries.X i)) = _
      rw [GeneralCoordinates.substitute_operator, SubstitutionBasic.substitute_X T hT.1, hfe]
    rw [hop]
    exact hf
  · change eta R u = g
    rw [GeneralCoordinates.eta_eq_substitute, he]

end Lax825748Proofs.Existence
