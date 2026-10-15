import Lax825748.ShuffleFiniteCoordinates
import Lax825748Proofs.GeneralCoordinates
import Lax825748Proofs.ResidualCoordinates

noncomputable section
namespace Lax825748Proofs.ShuffleFinite

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.ShuffleFinite Lax825748.FormalSeries
open Lax825748.DifferentialRepresentation Lax825748.RepresentationMap

theorem constant_mem {X : Type} (A : ShuffleSubalgebra X) (a : ℝ) :
    constantSeries a ∈ A.toSubmodule := by
  rw [← SubstitutionBasic.scalar_constant a]
  exact A.toSubmodule.smul_mem a A.one_mem

theorem word_residual_mem {X : Type} (A : ShuffleSubalgebra X) (hstable : DerivativeStable A)
    (w : Word X) (T : NCSeries X) (hT : T ∈ A.toSubmodule) :
    rightResidual T (wordPolynomial w) ∈ A.toSubmodule := by
  induction w using FreeMonoid.recOn generalizing T with
  | one =>
    have he : rightResidual T (wordPolynomial 1) = T := by
      funext u
      simp [rightResidual, ← Series.word_mul, Series.pairing_word]
    rw [he]
    exact hT
  | of_mul x w ih =>
    rw [Series.word_mul, ← Series.residual_mul]
    exact ih _ (hstable x T hT)

theorem residual_mem {X : Type} (A : ShuffleSubalgebra X) (hstable : DerivativeStable A)
    (T : NCSeries X) (hT : T ∈ A.toSubmodule) (Q : NCPolynomial X) :
    rightResidual T Q ∈ A.toSubmodule := by
  induction Q using MonoidAlgebra.induction_on with
  | of w => exact word_residual_mem A hstable w T hT
  | add Q U hQ hU =>
    have he : rightResidual T (Q + U) = rightResidual T Q + rightResidual T U := by
      funext w
      simp [rightResidual, add_mul]
    rw [he]
    exact A.toSubmodule.add_mem hQ hU
  | smul a Q hQ =>
    have he : rightResidual T (a • Q) = a • rightResidual T Q := by
      funext w
      simp [rightResidual]
    rw [he]
    exact A.toSubmodule.smul_mem a hQ

/--
---
conclusion: Lax825748.ShuffleFiniteCoordinates.coordinates_in_algebra
---
Choose finite polynomial functionals dual to a basis of the Lie residual
space. Centered prefix residuals belong to the witnessing algebra and form
a normalized coordinate family on the stabilizer annihilator.
-/
theorem coordinates_in_algebra {X : Type} {k : ℕ} (f : NCSeries X)
    (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A)
    (hstable : DerivativeStable A) (hf : f ∈ A.toSubmodule)
    (K : LieSubalgebraOfPolynomials X)
    (hK : ∀ L : LiePolynomial X, L ∈ K ↔ leftResidual L.val f = 0)
    (P : Fin k → LiePolynomial X) (hP : IsComplement K P) :
    ∃ (Q : Fin k → NCPolynomial X) (G : Fin k → NCSeries X),
      (∀ i, G i = rightResidual f (Q i) - constantSeries (pairing f (Q i))) ∧
      IsCoordinateFamily K P G ∧
      (∀ i, G i ∈ A.toSubmodule ∧ IsShuffleFinite (G i)) ∧
      (∀ T : NCSeries X, InAnnihilator K T ↔
        ∃! u : StateSeries k, substituteShuffle G u = T) := by
  obtain ⟨Q, hQ⟩ := ResidualCoordinates.dual_polynomials f K hK P hP
  let G := ResidualCoordinates.coordinates f Q
  have hG := ResidualCoordinates.coordinates_family f K hK P Q hQ
  have hmem (i : Fin k) : G i ∈ A.toSubmodule :=
    A.toSubmodule.sub_mem (residual_mem A hstable f hf (Q i)) (constant_mem A _)
  refine ⟨Q, G, fun _ => rfl, hG, ?_, ?_⟩
  · intro i
    exact ⟨hmem i, A, hfg, hstable, hmem i⟩
  · exact Lax825748.Annihilator.formal_coordinates K P hP G hG

/--
---
conclusion: Lax825748.ShuffleFiniteCoordinates.minimal_realization
---
Use the Lie residual kernel and a complement of size equal to the Lie rank.
The shuffle-finite normalized coordinates give a formal representation whose
state-coordinate series are exactly the chosen residual coordinates.
-/
theorem minimal_realization {X : Type} [Finite X] (f : NCSeries X) (k : ℕ)
    (hr : HasLieRank f k) (A : ShuffleSubalgebra X)
    (hfg : FinitelyGenerated A) (hstable : DerivativeStable A) (hf : f ∈ A.toSubmodule) :
    ∃ R : Representation X k, Represents R f ∧
      ∀ i : Fin k, eta R (MvPowerSeries.X i) ∈ A.toSubmodule ∧
        IsShuffleFinite (eta R (MvPowerSeries.X i)) := by
  obtain ⟨P, hP⟩ := ResidualKernel.complement_exists f k hr
  obtain ⟨Q, G, _, hG, hmem, _⟩ :=
    Lax825748.ShuffleFiniteCoordinates.coordinates_in_algebra f A hfg hstable hf
      (ResidualKernel.kernel f) (fun _ => Iff.rfl) P hP
  obtain ⟨R, hR, hcoords⟩ := GeneralCoordinates.realizes_in_coordinates
    (ResidualKernel.kernel f) P hP G hG f (ResidualKernel.series_ann f)
  refine ⟨R, hR, ?_⟩
  intro i
  rw [hcoords i]
  exact hmem i

end Lax825748Proofs.ShuffleFinite
