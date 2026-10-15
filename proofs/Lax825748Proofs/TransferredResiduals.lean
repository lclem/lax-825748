import Lax825748Proofs.SubstitutionBasic
import Lax825748Proofs.ContinuousDerivations

noncomputable section
namespace Lax825748Proofs.TransferredResiduals

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries Lax825748.Shuffle Lax825748.ShuffleIdentities
open CoordinateContinuity SubstitutionBasic SubstitutionAlgebra

variable {X : Type} {d : ℕ}
variable (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
variable (hP : IsComplement K P) (S : Fin d → NCSeries X)
variable (hS : IsCoordinateFamily K P S) (hPBW : IsPBWCoordinateFamily P S)

def operator (x : X) (f : StateSeries d) : StateSeries d :=
  moments P (rightResidual (substituteShuffle S f) (letter x))

include K hP hS hPBW in
theorem substitute_operator (x : X) (f : StateSeries d) :
    substituteShuffle S (operator P S x f) = rightResidual (substituteShuffle S f) (letter x) := by
  apply substitute_moments K P hP S hS hPBW
  exact Lax825748.Annihilator.closed_residual K _
    (SubstitutionFinite.substitute_ann K S hS.1 hS.2.1 f) _

theorem residual_add (T U : NCSeries X) (Q : NCPolynomial X) :
    rightResidual (T + U) Q = rightResidual T Q + rightResidual U Q := by
  funext w
  exact Series.pairing_add_series T U _

theorem residual_smul (a : ℝ) (T : NCSeries X) (Q : NCPolynomial X) :
    rightResidual (a • T) Q = a • rightResidual T Q := by
  funext w
  exact Series.pairing_smul_series a T _

theorem residual_constant (x : X) (a : ℝ) : rightResidual (constantSeries a) (letter x) = 0 := by
  rw [Shuffle.residual_letter_eq_shift]
  exact Shuffle.shift_constant x a

def derivation (x : X) : Derivation ℝ (StateSeries d) (StateSeries d) where
  toFun := operator P S x
  map_add' f g := by
    apply substitute_injective P S hS.1 hS.2.2 hPBW
    rw [substitute_operator K P hP S hS hPBW, substitute_add, substitute_add,
      substitute_operator K P hP S hS hPBW, substitute_operator K P hP S hS hPBW,
      residual_add]
  map_smul' a f := by
    apply substitute_injective P S hS.1 hS.2.2 hPBW
    rw [substitute_operator K P hP S hS hPBW, substitute_smul, substitute_smul,
      substitute_operator K P hP S hS hPBW, residual_smul]
    rfl
  map_one_eq_zero' := by
    change operator P S x 1 = 0
    apply substitute_injective P S hS.1 hS.2.2 hPBW
    rw [substitute_operator K P hP S hS hPBW, substitute_zero]
    change rightResidual (substituteShuffle S (MvPowerSeries.C 1)) (letter x) = 0
    rw [substitute_C S hS.1, residual_constant]
  leibniz' f g := by
    change operator P S x (f * g) = f * operator P S x g + g * operator P S x f
    apply substitute_injective P S hS.1 hS.2.2 hPBW
    rw [substitute_operator K P hP S hS hPBW, substitute_add,
      substitute_mul S hS.1, substitute_mul S hS.1, substitute_mul S hS.1,
      substitute_operator K P hP S hS hPBW, substitute_operator K P hP S hS hPBW,
      Lax825748.ShuffleIdentities.residual_derivation]
    rw [Lax825748.Shuffle.commutative (substituteShuffle S g), add_comm]

theorem operator_continuous (x : X) : Lax825748.FormalSeries.FormallyContinuous (operator P S x) := by
  intro n
  obtain ⟨m, hm⟩ := moments_agree P n
  refine ⟨m + 1, ?_⟩
  intro f g h
  apply hm
  intro w hw
  rw [Shuffle.residual_letter_eq_shift, Shuffle.residual_letter_eq_shift]
  exact CoordinateContinuity.substitute_agree S f g h (FreeMonoid.of x * w) (by
    simpa only [FreeMonoid.toList_of_mul, List.length_cons] using Nat.succ_lt_succ hw)

include K hP hS hPBW in
theorem operator_field (x : X) (f : StateSeries d) :
    operator P S x f = applyVectorField (fun i => operator P S x (MvPowerSeries.X i)) f :=
  ContinuousDerivations.derivation_eq_field (derivation K P hP S hS hPBW x)
    (operator_continuous P S x) f

end Lax825748Proofs.TransferredResiduals
