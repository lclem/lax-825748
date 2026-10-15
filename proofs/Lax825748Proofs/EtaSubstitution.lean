import Lax825748Proofs.SubstitutionBasic
import Lax825748Proofs.ContinuousDerivations

noncomputable section
namespace Lax825748Proofs.EtaSubstitution

open Lax825748.Series Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.RepresentationMap Lax825748.Annihilator
open SubstitutionBasic SubstitutionAlgebra

def coordinates {X : Type} {d : ℕ} (R : Representation X d) : Fin d → NCSeries X :=
  fun i => eta R (MvPowerSeries.X i)

theorem coordinates_zero {X : Type} {d : ℕ} (R : Representation X d) :
    ∀ i, coordinates R i 1 = 0 := by
  intro i
  simp [coordinates, eta]

theorem polynomial_eq {X : Type} {d : ℕ} (R : Representation X d)
    (p : MvPolynomial (Fin d) ℝ) :
    eta R p.toMvPowerSeries = substituteShuffle (coordinates R) p.toMvPowerSeries := by
  have hη := Lax825748.RepresentationMap.algebra_homomorphism R
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.coe_C, hη.1, substitute_C _ (coordinates_zero R)]
  | add p q hp hq => rw [MvPolynomial.coe_add, hη.2.1, substitute_add, hp, hq]
  | mul_X p i hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, hη.2.2,
      substitute_mul _ (coordinates_zero R), hp, substitute_X _ (coordinates_zero R)]
    rfl

theorem eta_eq_substitute {X : Type} {d : ℕ} (R : Representation X d) (f : StateSeries d) :
    eta R f = substituteShuffle (coordinates R) f := by
  funext w
  let n := w.toList.length + 1
  obtain ⟨m, hm⟩ := Lax825748.RepresentationMap.continuous R n
  let k := max m n
  let p := MvPowerSeries.truncTotal k f
  have hη := hm f p.toMvPowerSeries (ContinuousDerivations.trunc_agree f (le_max_left _ _))
    w (Nat.lt_succ_self _)
  have hs := CoordinateContinuity.substitute_agree (coordinates R) f p.toMvPowerSeries
    (ContinuousDerivations.trunc_agree f (le_max_right _ _)) w (Nat.lt_succ_self _)
  exact hη.trans ((congrArg (fun T : NCSeries X => T w) (polynomial_eq R p)).trans hs.symm)

end Lax825748Proofs.EtaSubstitution
