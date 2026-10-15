import Lax825748.CDACoefficients
import Lax825748Proofs.CDAChart

noncomputable section
namespace Lax825748Proofs.CDACoefficients

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.ShuffleFinite Lax825748.FormalSeries
open Lax825748.DifferentialRepresentation Lax825748.RepresentationMap Lax825748.CDA

/--
---
conclusion: Lax825748.CDACoefficients.coordinate_algebra
---
Extend the prescribed coordinates inside the shuffle algebra to a chart on
its common Lie stabilizer. Pull back the algebra, adjoin the reciprocal of
the frame determinant, and set the extra variables to zero.
-/
theorem coordinate_algebra {X : Type} {k : ℕ}
    (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A)
    (hstable : Lax825748.ShuffleFinite.DerivativeStable A)
    (K : LieSubalgebraOfPolynomials X) (P : Fin k → LiePolynomial X)
    (_hP : IsComplement K P) (G : Fin k → NCSeries X)
    (hG : IsCoordinateFamily K P G) (hmem : ∀ i, G i ∈ A.toSubmodule) :
    ∃ C : Subalgebra ℝ (StateSeries k), C.FG ∧ Lax825748.CDA.DerivativeStable C ∧
      ∀ u : StateSeries k, substituteShuffle G u ∈ A.toSubmodule → u ∈ C := by
  obtain ⟨m, e, L, Q, S, hQ, hS, hSmem, he, hann⟩ :=
    CDAAmbient.ambient_coordinates A hfg hstable G hG.1 P hG.2.2 hmem
  obtain ⟨B, hBfg, hBs, hBmem⟩ :=
    CDAChart.chart_algebra A hfg hstable L Q hQ S hS hSmem hann
  obtain ⟨hCfg, hCs⟩ := CDAAlgebra.restrict_algebra e B hBfg hBs
  refine ⟨B.map (MvPowerSeries.killCompl e), hCfg, hCs, ?_⟩
  intro u hu
  have hr : substituteShuffle S (MvPowerSeries.rename e u) = substituteShuffle G u := by
    rw [CDASubstitution.substitute_rename S hS.1 e u]
    exact congrArg (fun T => substituteShuffle T u) (funext he)
  exact ⟨MvPowerSeries.rename e u, hBmem _ (hr.symm ▸ hu),
    MvPowerSeries.killCompl_rename_app u⟩

/--
---
conclusion: Lax825748.CDACoefficients.minimal_realization
---
Choose normalized residual coordinates in the witnessing shuffle algebra.
The output and every coordinate residual pull back into the common CDA
algebra supplied by the coordinate theorem.
-/
theorem minimal_realization {X : Type} [Finite X] (f : NCSeries X) (k : ℕ)
    (hr : HasLieRank f k) (A : ShuffleSubalgebra X)
    (hfg : FinitelyGenerated A) (hstable : Lax825748.ShuffleFinite.DerivativeStable A)
    (hf : f ∈ A.toSubmodule) :
    ∃ R : Representation X k, Represents R f ∧ IsCDA R.output ∧
      (∀ (x : X) (i : Fin k), IsCDA (R.fields x i)) ∧
      ∀ i : Fin k, eta R (MvPowerSeries.X i) ∈ A.toSubmodule ∧
        IsShuffleFinite (eta R (MvPowerSeries.X i)) := by
  obtain ⟨P, hP⟩ := ResidualKernel.complement_exists f k hr
  let K := ResidualKernel.kernel f
  obtain ⟨Q, G, _, hG, hmem, _⟩ :=
    Lax825748.ShuffleFiniteCoordinates.coordinates_in_algebra f A hfg hstable hf
      K (fun _ => Iff.rfl) P hP
  obtain ⟨C, hCfg, hCs, hCmem⟩ :=
    Lax825748.CDACoefficients.coordinate_algebra A hfg hstable K P hP G hG
      (fun i => (hmem i).1)
  let u := GeneralCoordinates.inverse K P hP G hG f (ResidualKernel.series_ann f)
  let R := GeneralCoordinates.representation K P hP G hG u
  have hu : substituteShuffle G u = f :=
    GeneralCoordinates.substitute_inverse K P hP G hG f (ResidualKernel.series_ann f)
  refine ⟨R, ?_, ⟨C, hCfg, hCs, hCmem u (hu.symm ▸ hf)⟩, ?_, ?_⟩
  · change eta R u = f
    rw [GeneralCoordinates.eta_eq_substitute, hu]
  · intro x i
    refine ⟨C, hCfg, hCs, hCmem _ ?_⟩
    change substituteShuffle G (GeneralCoordinates.operator K P hP G hG x (MvPowerSeries.X i)) ∈
      A.toSubmodule
    rw [GeneralCoordinates.substitute_operator, SubstitutionBasic.substitute_X G hG.1]
    exact hstable x (G i) (hmem i).1
  · intro i
    rw [GeneralCoordinates.eta_eq_substitute, SubstitutionBasic.substitute_X G hG.1]
    exact hmem i

end Lax825748Proofs.CDACoefficients
