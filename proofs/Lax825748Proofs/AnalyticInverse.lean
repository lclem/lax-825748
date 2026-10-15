import Lax825748Proofs.InverseFrame
import Lax825748Proofs.TaylorCoefficients
import Lax825748.FactorialEstimate
import Lax825748.ConvergenceHypothesis

noncomputable section

namespace Lax825748Proofs.AnalyticInverse

open Lax825748.Series Lax825748.FormalSeries Lax825748.Monomials
open Lax825748.CoordinateChange Lax825748.DifferentialRepresentation
open Lax825748.ConvergentSeries Lax825748.AnalyticRepresentations
open InverseFrame TaylorCoefficients

theorem inverse_intertwining {d : ℕ} (φ : FormalChange d) (u f : StateSeries d)
    (w : Word (Fin d)) :
    act (derivativeRepresentation d) (φ.toAlgEquiv.symm f) w =
      φ.toAlgEquiv.symm (act (⟨frame φ, u⟩ : Representation (Fin d) d) f w) := by
  induction w using FreeMonoid.recOn generalizing f with
  | one => rfl
  | of_mul i w ih =>
    rw [Lax825748Proofs.RepresentationMap.act_cons, derivative_field,
      Lax825748Proofs.RepresentationMap.act_cons]
    have he : MvPowerSeries.pderiv ℝ i (φ.toAlgEquiv.symm f) =
        φ.toAlgEquiv.symm (applyVectorField (frame φ i) f) := by
      rw [← conjugate_field]
      change _ = φ.toAlgEquiv.symm (φ.toAlgEquiv _)
      rw [AlgEquiv.symm_apply_apply]
    rw [he, ih]

theorem inverse_series {d : ℕ} (φ : FormalChange d)
    (hφ : ∀ i, Convergent (φ.toAlgEquiv (MvPowerSeries.X i)))
    (f : StateSeries d) (hf : Convergent f) : Convergent (φ.toAlgEquiv.symm f) := by
  let R : Representation (Fin d) d := ⟨frame φ, f⟩
  have ha : IsAnalytic R := ⟨hf, frame_convergent φ hφ⟩
  obtain ⟨α, hα, C, hC, hb⟩ := Lax825748.FactorialEstimate.factorial_bound R ha
  refine ⟨α, hα, C * ((d : ℝ) + 1), by positivity, ?_⟩
  intro I
  obtain ⟨w, hw, ht⟩ := derivative_word I
  have he : generatingSeries R w =
      (multiFactorial I : ℝ) * MvPowerSeries.coeff I (φ.toAlgEquiv.symm f) := by
    calc
      _ = MvPowerSeries.constantCoeff (φ.toAlgEquiv.symm (act R f w)) :=
        (constant_preserving φ.toAlgEquiv.symm.toAlgHom φ.continuous_invFun φ.inverse_origin _).symm
      _ = MvPowerSeries.constantCoeff (act (derivativeRepresentation d) (φ.toAlgEquiv.symm f) w) :=
        congrArg MvPowerSeries.constantCoeff (inverse_intertwining φ f f w).symm
      _ = _ := ht _
  have hi : 0 < (multiFactorial I : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => Nat.factorial_pos (I i))
  have hfact : ((totalDegree I).factorial : ℝ) ≤
      ((d : ℝ) + 1) ^ totalDegree I * (multiFactorial I : ℝ) := by
    have hn := (Lax825748.ConvergenceHypothesis.factorial_comparison I).2
    have hn' : (totalDegree I).factorial ≤ (d + 1) ^ totalDegree I * multiFactorial I := by
      refine hn.trans ?_
      gcongr
      omega
    exact_mod_cast hn'
  apply (mul_le_mul_iff_left₀ hi).mp
  calc
    _ = |generatingSeries R w| := by rw [he, abs_mul, abs_of_pos hi]; ring
    _ ≤ α * C ^ totalDegree I * ((totalDegree I).factorial : ℝ) := by
      simpa only [hw] using hb w
    _ ≤ α * C ^ totalDegree I *
        (((d : ℝ) + 1) ^ totalDegree I * (multiFactorial I : ℝ)) :=
      mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = _ := by rw [mul_pow]; ring

/--
---
conclusion: Lax825748.AnalyticChanges.inverse_convergent
---
Conjugate the coordinate derivations by the formal automorphism. Their
coefficients form the inverse Jacobian, which converges by the adjugate
formula and reciprocal convergence. The factorial estimate for these vector
fields bounds the Taylor coefficients of each inverse coordinate geometrically.
-/
theorem inverse_convergent {d : ℕ} (φ : FormalChange d)
    (hφ : ∀ i, Convergent (φ.toAlgEquiv (MvPowerSeries.X i))) :
    ∀ i, Convergent (φ.toAlgEquiv.symm (MvPowerSeries.X i)) :=
  fun i => inverse_series φ hφ _ (PowerSeriesBounds.convergent_X i)

end Lax825748Proofs.AnalyticInverse
