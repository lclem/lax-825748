import Lax825748Proofs.TransferredResiduals
import Lax825748Proofs.InverseContinuity

noncomputable section
namespace Lax825748Proofs.GeneralCoordinates

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.RepresentationMap
open SubstitutionBasic SubstitutionAlgebra

variable {X : Type} {d : ℕ}
variable (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
variable (hP : IsComplement K P) (S : Fin d → NCSeries X)
variable (hS : IsCoordinateFamily K P S)

include K hP hS in
theorem substitute_injective : Function.Injective (substituteShuffle S) := by
  intro f g hfg
  obtain ⟨u, hu, huniq⟩ := (Lax825748.Annihilator.formal_coordinates K P hP S hS
    (substituteShuffle S f)).mp (SubstitutionFinite.substitute_ann K S hS.1 hS.2.1 f)
  exact (huniq f rfl).trans (huniq g hfg.symm).symm

def inverse (T : NCSeries X) (hT : InAnnihilator K T) : StateSeries d :=
  Classical.choose ((Lax825748.Annihilator.formal_coordinates K P hP S hS T).mp hT)

theorem substitute_inverse (T : NCSeries X) (hT : InAnnihilator K T) :
    substituteShuffle S (inverse K P hP S hS T hT) = T :=
  (Classical.choose_spec ((Lax825748.Annihilator.formal_coordinates K P hP S hS T).mp hT)).1

def operator (x : X) (f : StateSeries d) : StateSeries d :=
  inverse K P hP S hS (rightResidual (substituteShuffle S f) (letter x))
    (Lax825748.Annihilator.closed_residual K _
      (SubstitutionFinite.substitute_ann K S hS.1 hS.2.1 f) _)

theorem substitute_operator (x : X) (f : StateSeries d) :
    substituteShuffle S (operator K P hP S hS x f) =
      rightResidual (substituteShuffle S f) (letter x) :=
  substitute_inverse K P hP S hS _ _

def derivation (x : X) : Derivation ℝ (StateSeries d) (StateSeries d) where
  toFun := operator K P hP S hS x
  map_add' f g := by
    apply substitute_injective K P hP S hS
    rw [substitute_operator, substitute_add, substitute_add,
      substitute_operator, substitute_operator, TransferredResiduals.residual_add]
  map_smul' a f := by
    apply substitute_injective K P hP S hS
    rw [substitute_operator, substitute_smul, substitute_smul,
      substitute_operator, TransferredResiduals.residual_smul]
    rfl
  map_one_eq_zero' := by
    change operator K P hP S hS x 1 = 0
    apply substitute_injective K P hP S hS
    rw [substitute_operator, substitute_zero]
    change rightResidual (substituteShuffle S (MvPowerSeries.C 1)) (letter x) = 0
    rw [substitute_C S hS.1, TransferredResiduals.residual_constant]
  leibniz' f g := by
    change operator K P hP S hS x (f * g) =
      f * operator K P hP S hS x g + g * operator K P hP S hS x f
    apply substitute_injective K P hP S hS
    rw [substitute_operator, substitute_add,
      substitute_mul S hS.1, substitute_mul S hS.1, substitute_mul S hS.1,
      substitute_operator, substitute_operator, Lax825748.ShuffleIdentities.residual_derivation]
    rw [Lax825748.Shuffle.commutative (substituteShuffle S g), add_comm]

theorem operator_continuous (x : X) :
    Lax825748.FormalSeries.FormallyContinuous (operator K P hP S hS x) := by
  intro n
  obtain ⟨m, hm⟩ := InverseContinuity.substitute_inverse_continuous P S hS.1 hS.2.2 n
  refine ⟨m + 1, ?_⟩
  intro f g h
  apply hm
  rw [substitute_operator, substitute_operator]
  intro w hw
  rw [Shuffle.residual_letter_eq_shift, Shuffle.residual_letter_eq_shift]
  exact CoordinateContinuity.substitute_agree S f g h (FreeMonoid.of x * w) (by
    simpa only [FreeMonoid.toList_of_mul, List.length_cons] using Nat.succ_lt_succ hw)

theorem operator_field (x : X) (f : StateSeries d) :
    operator K P hP S hS x f =
      applyVectorField (fun i => operator K P hP S hS x (MvPowerSeries.X i)) f :=
  ContinuousDerivations.derivation_eq_field (derivation K P hP S hS x)
    (operator_continuous K P hP S hS x) f

def representation (f : StateSeries d) : Representation X d where
  fields x i := operator K P hP S hS x (MvPowerSeries.X i)
  output := f

theorem act_substitute (f u : StateSeries d) (w : Word X) :
    substituteShuffle S (act (representation K P hP S hS f) u w) =
      rightResidual (substituteShuffle S u) (wordPolynomial w) := by
  induction w using FreeMonoid.recOn generalizing u with
  | one =>
    funext v
    simp [rightResidual, ← Series.word_mul, Series.pairing_word]
  | of_mul x w ih =>
    rw [RepresentationMap.act_cons]
    change substituteShuffle S (act (representation K P hP S hS f)
      (applyVectorField (fun i => operator K P hP S hS x (MvPowerSeries.X i)) u) w) = _
    rw [← operator_field K P hP S hS, ih, substitute_operator, Series.residual_mul]
    rw [Series.word_mul]
    rfl

theorem eta_eq_substitute (f u : StateSeries d) :
    eta (representation K P hP S hS f) u = substituteShuffle S u := by
  funext w
  have hh := congrArg (fun T : NCSeries X => T 1) (act_substitute K P hP S hS f u w)
  rw [substitute_empty S hS.1] at hh
  simpa [eta, rightResidual, ← Series.word_mul, Series.pairing_word] using hh

include P hP hS in
theorem realizes_in_coordinates (f : NCSeries X) (hf : InAnnihilator K f) :
    ∃ R : Representation X d, Represents R f ∧ ∀ i, eta R (MvPowerSeries.X i) = S i := by
  let u := inverse K P hP S hS f hf
  refine ⟨representation K P hP S hS u, ?_, ?_⟩
  · change eta (representation K P hP S hS u) u = f
    rw [eta_eq_substitute, substitute_inverse]
  · intro i
    rw [eta_eq_substitute, substitute_X S hS.1]

end Lax825748Proofs.GeneralCoordinates
