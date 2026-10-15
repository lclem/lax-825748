import Lax825748.FormalRealization
import Lax825748Proofs.TransferredResiduals
import Lax825748Proofs.ResidualKernel

noncomputable section
namespace Lax825748Proofs.FormalExistence

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open CoordinateContinuity SubstitutionBasic TransferredResiduals

variable {X : Type} {d : ℕ}
variable (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
variable (hP : IsComplement K P) (S : Fin d → NCSeries X)
variable (hS : IsCoordinateFamily K P S) (hPBW : IsPBWCoordinateFamily P S)

def representation (f : StateSeries d) : Representation X d where
  fields x i := operator P S x (MvPowerSeries.X i)
  output := f

include K hP hS hPBW in
theorem act_substitute (f k : StateSeries d) (w : Word X) :
    substituteShuffle S (act (representation P S f) k w) =
      rightResidual (substituteShuffle S k) (wordPolynomial w) := by
  induction w using FreeMonoid.recOn generalizing k with
  | one =>
    funext u
    simp [rightResidual, ← Series.word_mul, Series.pairing_word]
  | of_mul x w ih =>
    rw [RepresentationMap.act_cons]
    change substituteShuffle S (act (representation P S f)
      (applyVectorField (fun i => operator P S x (MvPowerSeries.X i)) k) w) = _
    rw [← operator_field K P hP S hS hPBW, ih,
      substitute_operator K P hP S hS hPBW, Series.residual_mul]
    rw [Series.word_mul]
    rfl

include hP hS hPBW in
theorem represents (g : NCSeries X) (hg : InAnnihilator K g) :
    Represents (representation P S (moments P g)) g := by
  funext w
  have hh := congrArg (fun T : NCSeries X => T 1)
    (act_substitute K P hP S hS hPBW (moments P g) (moments P g) w)
  rw [substitute_empty S hS.1, substitute_moments K P hP S hS hPBW g hg] at hh
  simpa [rightResidual, generatingSeries, ← Series.word_mul, Series.pairing_word, representation] using hh

/--
---
conclusion: Lax825748.FormalRealization.existence
---
Take the kernel of the Lie residual map. Its quotient has the prescribed
rank. PBW coordinates identify its annihilator with formal state series;
right residuals transfer to continuous derivations, hence to vector fields.
-/
theorem existence {X : Type} [Finite X] (g : NCSeries X) (d : ℕ) (hr : HasLieRank g d) :
    ∃ R : Representation X d, Represents R g := by
  obtain ⟨P, hP⟩ := ResidualKernel.complement_exists g d hr
  obtain ⟨S, hS, hPBW⟩ := Lax825748.Annihilator.coordinates_exist (ResidualKernel.kernel g) P hP
  exact ⟨representation P S (moments P g),
    represents (ResidualKernel.kernel g) P hP S hS hPBW g (ResidualKernel.series_ann g)⟩

end Lax825748Proofs.FormalExistence
