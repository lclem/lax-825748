import Lax825748.AnalyticCoordinates
import Lax825748Proofs.CoordinateEquivalence

noncomputable section

namespace Lax825748Proofs.AnalyticCoordinates

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries Lax825748.ConvergentSeries
open Lax825748Proofs

/--
---
conclusion: Lax825748.AnalyticCoordinates.expansion_converges
---
The coordinate expressions in PBW coordinates converge. Transfer from the
given coordinates to PBW coordinates is a formal change with convergent
coordinate images. Apply analytic inversion and convergent composition.
-/
theorem expansion_converges {X : Type} {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (T : Fin d → NCSeries X)
    (hT : IsCoordinateFamily K P T)
    (hCT : ∀ i, Lax825748.ConvergenceHypothesis.Holds (T i))
    (U : NCSeries X) (hU : InAnnihilator K U)
    (hCU : Lax825748.ConvergenceHypothesis.Holds U) :
    ∃ f : StateSeries d, Convergent f ∧ substituteShuffle T f = U := by
  obtain ⟨S, hS, hPBW⟩ := Lax825748.Annihilator.coordinates_exist K P hP
  let φ := CoordinateEquivalence.formalChange K P hP T S hT hS
  have hφ : ∀ i, Convergent (φ.toAlgEquiv (MvPowerSeries.X i)) := by
    intro i
    obtain ⟨f, hf, he⟩ := Lax825748.PBWConvergence.expansion_converges
      K P hP S hS hPBW (T i) (hT.2.1 i) (hCT i)
    have heq : φ.toAlgEquiv (MvPowerSeries.X i) = f := by
      apply GeneralCoordinates.substitute_injective K P hP S hS
      change substituteShuffle S (CoordinateEquivalence.transfer K P hP T S hT hS
        (MvPowerSeries.X i)) = _
      rw [CoordinateEquivalence.transfer_substitute, SubstitutionBasic.substitute_X T hT.1, he]
    rw [heq]
    exact hf
  obtain ⟨f, hf, he⟩ := Lax825748.PBWConvergence.expansion_converges
    K P hP S hS hPBW U hU hCU
  refine ⟨φ.toAlgEquiv.symm f, ?_, ?_⟩
  · exact Lax825748.AnalyticCalculus.composition φ.toAlgEquiv.symm.toAlgHom
      φ.continuous_invFun φ.inverse_origin
      (Lax825748.AnalyticChanges.inverse_convergent φ hφ) f hf
  · change substituteShuffle T (CoordinateEquivalence.transfer K P hP S T hS hT f) = U
    rw [CoordinateEquivalence.transfer_substitute, he]

end Lax825748Proofs.AnalyticCoordinates
