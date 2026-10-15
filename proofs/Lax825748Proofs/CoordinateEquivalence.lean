import Lax825748.CoordinateChange
import Lax825748Proofs.GeneralCoordinates

noncomputable section

namespace Lax825748Proofs.CoordinateEquivalence

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries Lax825748.CoordinateChange
open Lax825748Proofs SubstitutionBasic SubstitutionAlgebra

variable {X : Type} {d : ℕ}
variable (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
variable (hP : IsComplement K P) (S T : Fin d → NCSeries X)
variable (hS : IsCoordinateFamily K P S) (hT : IsCoordinateFamily K P T)

def transfer (f : StateSeries d) : StateSeries d :=
  GeneralCoordinates.inverse K P hP T hT (substituteShuffle S f)
    (SubstitutionFinite.substitute_ann K S hS.1 hS.2.1 f)

theorem transfer_substitute (f : StateSeries d) :
    substituteShuffle T (transfer K P hP S T hS hT f) = substituteShuffle S f :=
  GeneralCoordinates.substitute_inverse K P hP T hT _ _

def algebraEquiv : StateSeries d ≃ₐ[ℝ] StateSeries d where
  toFun := transfer K P hP S T hS hT
  invFun := transfer K P hP T S hT hS
  left_inv f := by
    apply GeneralCoordinates.substitute_injective K P hP S hS
    rw [transfer_substitute, transfer_substitute]
  right_inv f := by
    apply GeneralCoordinates.substitute_injective K P hP T hT
    rw [transfer_substitute, transfer_substitute]
  map_mul' f g := by
    apply GeneralCoordinates.substitute_injective K P hP T hT
    rw [transfer_substitute, substitute_mul S hS.1, substitute_mul T hT.1,
      transfer_substitute, transfer_substitute]
  map_add' f g := by
    apply GeneralCoordinates.substitute_injective K P hP T hT
    rw [transfer_substitute, substitute_add, substitute_add,
      transfer_substitute, transfer_substitute]
  commutes' a := by
    apply GeneralCoordinates.substitute_injective K P hP T hT
    change substituteShuffle T (transfer K P hP S T hS hT (MvPowerSeries.C a)) =
      substituteShuffle T (MvPowerSeries.C a)
    rw [transfer_substitute, substitute_C S hS.1, substitute_C T hT.1]

theorem transfer_continuous :
    Lax825748.FormalSeries.FormallyContinuous (transfer K P hP S T hS hT) := by
  intro n
  obtain ⟨m, hm⟩ := InverseContinuity.substitute_inverse_continuous P T hT.1 hT.2.2 n
  refine ⟨m, ?_⟩
  intro f g h
  apply hm
  rw [transfer_substitute, transfer_substitute]
  exact CoordinateContinuity.substitute_agree S f g h

theorem transfer_origin (i : Fin d) :
    MvPowerSeries.constantCoeff (transfer K P hP S T hS hT (MvPowerSeries.X i)) = 0 := by
  have he := congrArg (fun U : NCSeries X => U 1)
    (transfer_substitute K P hP S T hS hT (MvPowerSeries.X i))
  rw [substitute_empty T hT.1, substitute_X S hS.1, hS.1 i] at he
  exact he

def formalChange : FormalChange d where
  toAlgEquiv := algebraEquiv K P hP S T hS hT
  continuous_toFun := transfer_continuous K P hP S T hS hT
  continuous_invFun := transfer_continuous K P hP T S hT hS
  origin := transfer_origin K P hP S T hS hT
  inverse_origin := transfer_origin K P hP T S hT hS

end Lax825748Proofs.CoordinateEquivalence
