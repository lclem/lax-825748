import Lax825748Proofs.CDAAmbient
import Lax825748Proofs.CDASubstitution

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Lax825748Proofs.CDAChart

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.ShuffleFinite Lax825748.FormalSeries
open Lax825748.DifferentialRepresentation Lax825748.RepresentationMap

def substitutionHom {X : Type} {m : ℕ} (S : Fin m → NCSeries X)
    (hS : ∀ i, S i 1 = 0) : StateSeries m →ₐ[ℝ] ShuffleAlgebra.Algebra X where
  toFun := substituteShuffle S
  map_zero' := SubstitutionBasic.substitute_zero S
  map_one' := SubstitutionBasic.substitute_C S hS 1
  map_add' := SubstitutionAlgebra.substitute_add S
  map_mul' := SubstitutionAlgebra.substitute_mul S hS
  commutes' a := by
    change substituteShuffle S (MvPowerSeries.C a) = a • constantSeries 1
    rw [SubstitutionBasic.substitute_C S hS, SubstitutionBasic.scalar_constant]

theorem operator_substitute {X : Type} {m : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin m → LiePolynomial X)
    (hP : IsComplement K P) (S : Fin m → NCSeries X) (hS : IsCoordinateFamily K P S)
    (v f : StateSeries m) (Q : NCPolynomial X) :
    substituteShuffle S (Operators.operator (GeneralCoordinates.representation K P hP S hS v) Q f) =
      rightResidual (substituteShuffle S f) Q := by
  induction Q using MonoidAlgebra.induction_on with
  | of w =>
    change substituteShuffle S
        (Operators.operator (GeneralCoordinates.representation K P hP S hS v) (wordPolynomial w) f) =
      rightResidual (substituteShuffle S f) (wordPolynomial w)
    rw [Operators.operator_word]
    exact GeneralCoordinates.act_substitute K P hP S hS v f w
  | add Q T hQ hT =>
    rw [map_add, LinearMap.add_apply, SubstitutionAlgebra.substitute_add, hQ, hT]
    funext w
    simp [rightResidual, add_mul]
  | smul a Q hQ =>
    rw [map_smul, LinearMap.smul_apply, SubstitutionBasic.substitute_smul, hQ]
    funext w
    simp [rightResidual]

theorem chart_algebra {X : Type} {m : ℕ}
    (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A) (hs : DerivativeStable A)
    (K : LieSubalgebraOfPolynomials X) (P : Fin m → LiePolynomial X)
    (hP : IsComplement K P) (S : Fin m → NCSeries X) (hS : IsCoordinateFamily K P S)
    (hmem : ∀ i, S i ∈ A.toSubmodule)
    (hann : ∀ a ∈ A.toSubmodule, InAnnihilator K a) :
    ∃ C : Subalgebra ℝ (StateSeries m), C.FG ∧ Lax825748.CDA.DerivativeStable C ∧
      ∀ u, substituteShuffle S u ∈ A.toSubmodule → u ∈ C := by
  classical
  let Φ := substitutionHom S hS.1
  let B := (CDAAmbient.asAlgebra A).comap Φ
  have hmap : B.map Φ = CDAAmbient.asAlgebra A := by
    ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro ha
      have ha' : a ∈ A.toSubmodule := ha
      let u := GeneralCoordinates.inverse K P hP S hS a (hann a ha')
      have hu : Φ u = a := GeneralCoordinates.substitute_inverse K P hP S hS a (hann a ha')
      exact ⟨u, (show Φ u ∈ CDAAmbient.asAlgebra A from hu.symm ▸ ha), hu⟩
  have hBfg : B.FG := Subalgebra.fg_of_fg_map B Φ
    (GeneralCoordinates.substitute_injective K P hP S hS)
    (hmap.symm ▸ CDAAmbient.asAlgebra_fg A hfg)
  have hBX (i : Fin m) : MvPowerSeries.X i ∈ B := by
    change substituteShuffle S (MvPowerSeries.X i) ∈ A.toSubmodule
    rw [SubstitutionBasic.substitute_X S hS.1]
    exact hmem i
  let R := GeneralCoordinates.representation K P hP S hS 0
  choose V hV using fun j : Fin m => Operators.lie_operator_field R (P j)
  have hstable (j : Fin m) (u : StateSeries m) (hu : u ∈ B) :
      applyVectorField (V j) u ∈ B := by
    change substituteShuffle S (applyVectorField (V j) u) ∈ A.toSubmodule
    rw [← hV j u, operator_substitute]
    exact ShuffleFinite.residual_mem A hs _ hu (P j).val
  have hzero (i j : Fin m) :
      MvPowerSeries.constantCoeff (V i j) = if i = j then 1 else 0 := by
    have hh := Rank.pairing_operator R (MvPowerSeries.X j) (P i).val
    rw [GeneralCoordinates.eta_eq_substitute, SubstitutionBasic.substitute_X S hS.1,
      hV i, ContinuousDerivations.field_X, hS.2.2] at hh
    simpa only [eq_comm] using hh.symm
  obtain ⟨C, hC, hCs, hBC⟩ := CDAAlgebra.localize_frame B hBfg hBX V hstable hzero
  exact ⟨C, hC, hCs, fun _ hu => hBC hu⟩

end Lax825748Proofs.CDAChart
