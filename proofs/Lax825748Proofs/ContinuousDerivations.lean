import Lax825748Proofs.SubstitutionAlgebra
import Lax825748Proofs.RepresentationMap

noncomputable section
namespace Lax825748Proofs.ContinuousDerivations

open Lax825748.FormalSeries Lax825748.Monomials
open scoped BigOperators

theorem field_X {d : ℕ} (A : VectorField d) (i : Fin d) :
    applyVectorField A (MvPowerSeries.X i) = A i := by
  simp [applyVectorField, MvPowerSeries.pderiv_X, Pi.single_apply]

theorem polynomial_eq {d : ℕ} (D : Derivation ℝ (StateSeries d) (StateSeries d))
    (p : MvPolynomial (Fin d) ℝ) :
    D p.toMvPowerSeries = applyVectorField (fun i => D (MvPowerSeries.X i)) p.toMvPowerSeries := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.coe_C, RepresentationMap.field_C]
    exact D.map_algebraMap a
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, map_add, RepresentationMap.field_add, hp, hq]
  | mul_X p i hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, smul_eq_mul,
      RepresentationMap.field_mul, field_X, hp]
    ring

theorem trunc_agree {d : ℕ} (f : StateSeries d) {n m : ℕ} (hn : n ≤ m) :
    Lax825748.FormalSeries.AgreeBelow n f (MvPowerSeries.truncTotal m f).toMvPowerSeries := by
  intro I hI
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ (by
    rw [TriangularSystem.degree_eq_total]; omega)]

theorem derivation_eq_field {d : ℕ} (D : Derivation ℝ (StateSeries d) (StateSeries d))
    (hc : Lax825748.FormalSeries.FormallyContinuous D) (f : StateSeries d) :
    D f = applyVectorField (fun i => D (MvPowerSeries.X i)) f := by
  ext I
  let n := totalDegree I + 1
  obtain ⟨m, hm⟩ := hc n
  let k := max m (n + 1)
  let p := MvPowerSeries.truncTotal k f
  have hD := hm f p.toMvPowerSeries (trunc_agree f (le_max_left _ _)) I (Nat.lt_succ_self _)
  have hA := RepresentationMap.agree_field (fun i => D (MvPowerSeries.X i)) f p.toMvPowerSeries
    (trunc_agree f (le_max_right _ _)) I (Nat.lt_succ_self _)
  exact hD.trans ((congrArg (MvPowerSeries.coeff I) (polynomial_eq D p)).trans hA.symm)

end Lax825748Proofs.ContinuousDerivations
