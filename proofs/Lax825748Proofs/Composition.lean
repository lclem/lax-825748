import Lax825748Proofs.WeightedMass
import Lax208278Proofs.ContinuousDerivations

noncomputable section

namespace Lax825748Proofs.Composition

open Lax208278.FormalSeries Lax208278.Monomials Lax825748.ConvergentSeries
open WeightedMass
open scoped BigOperators

theorem image_monomial {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    (J : Fin d →₀ ℕ) (a : ℝ) :
    φ (MvPowerSeries.monomial J a) = a • ∏ i, φ (MvPowerSeries.X i) ^ J i := by
  rw [MvPowerSeries.monomial_eq', Finsupp.prod_fintype _ _ (by simp)]
  simp only [map_mul, map_prod, map_pow]
  rw [show φ (MvPowerSeries.C a) = MvPowerSeries.C a from φ.commutes a,
    MvPowerSeries.smul_eq_C_mul]

theorem monomial_weight_bound {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    {r ρ : ℝ} (hr : 0 ≤ r) (_hρ : 0 ≤ ρ)
    (hφ : ∀ i, AtRadius (φ (MvPowerSeries.X i)) r ∧ mass (φ (MvPowerSeries.X i)) r ≤ ρ)
    (J : Fin d →₀ ℕ) (a : ℝ) (I : Fin e →₀ ℕ) :
    weight (φ (MvPowerSeries.monomial J a)) r I ≤ |a| * ρ ^ totalDegree J := by
  rw [image_monomial]
  have hp : AtRadius (∏ i, φ (MvPowerSeries.X i) ^ J i) r :=
    AtRadius.prod _ _ (fun i _ => (hφ i).1.pow hr _) hr
  have hb : mass (∏ i, φ (MvPowerSeries.X i) ^ J i) r ≤ ρ ^ totalDegree J := by
    calc
      _ ≤ ∏ i, mass (φ (MvPowerSeries.X i) ^ J i) r :=
        mass_prod_le _ _ (fun i _ => (hφ i).1.pow hr _) hr
      _ ≤ ∏ i, ρ ^ J i := by
        apply Finset.prod_le_prod (fun i _ => mass_nonnegative _ hr)
        intro i _
        exact (mass_pow_le (hφ i).1 hr _).trans
          (pow_le_pow_left₀ (mass_nonnegative _ hr) (hφ i).2 _)
      _ = _ := (Finset.prod_pow_eq_pow_sum _ _ _)
  calc
    _ = |a| * weight (∏ i, φ (MvPowerSeries.X i) ^ J i) r I := by
      simp only [weight, MvPowerSeries.coeff_smul, abs_mul]; ring
    _ ≤ |a| * ρ ^ totalDegree J :=
      mul_le_mul_of_nonneg_left ((weight_le_mass hr hp I).trans hb) (abs_nonneg _)

theorem polynomial_weight_bound {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 ≤ ρ)
    (hφ : ∀ i, AtRadius (φ (MvPowerSeries.X i)) r ∧ mass (φ (MvPowerSeries.X i)) r ≤ ρ)
    (p : MvPolynomial (Fin d) ℝ) (I : Fin e →₀ ℕ) :
    weight (φ p.toMvPowerSeries) r I ≤
      ∑ J ∈ p.support, |MvPolynomial.coeff J p| * ρ ^ totalDegree J := by
  have he : φ p.toMvPowerSeries =
      ∑ J ∈ p.support, φ (MvPowerSeries.monomial J (MvPolynomial.coeff J p)) := by
    conv_lhs => rw [p.as_sum]
    change φ (MvPolynomial.coeToMvPowerSeries.ringHom _) = _
    rw [map_sum, map_sum]
    simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
  rw [he]
  unfold weight
  rw [map_sum]
  calc
    _ ≤ (∑ J ∈ p.support,
        |MvPowerSeries.coeff I (φ (MvPowerSeries.monomial J (MvPolynomial.coeff J p)))|) *
          r ^ totalDegree I :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hr _)
    _ = ∑ J ∈ p.support, weight (φ (MvPowerSeries.monomial J (MvPolynomial.coeff J p))) r I :=
      Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum fun J _ => monomial_weight_bound φ hr hρ hφ J _ I

/--
---
conclusion: Lax825748.AnalyticCalculus.composition
---
Shrink the target polyradius until each substituted coordinate has weighted
absolute sum at most a convergence radius of the input. Polynomial truncations
then have uniformly bounded coefficients, and formal continuity transfers the
bound to the full substituted series.
-/
theorem composition {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    (hc : FormallyContinuous φ)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ (MvPowerSeries.X i)) = 0)
    (hφ : ∀ i, Convergent (φ (MvPowerSeries.X i)))
    (f : StateSeries d) (hf : Convergent f) : Convergent (φ f) := by
  obtain ⟨ρ, hρ, hs⟩ := (Lax825748.AnalyticCalculus.absolute_convergence f).mp hf
  obtain ⟨r, hr, hb⟩ := common_small_radius (fun i => φ (MvPowerSeries.X i)) hφ h0 hρ
  have hM : 0 ≤ mass f ρ := mass_nonnegative f hρ.le
  refine ⟨mass f ρ + 1, by positivity, r⁻¹, inv_pos.mpr hr, ?_⟩
  intro I
  rw [inv_pow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  obtain ⟨m, hm⟩ := hc (totalDegree I + 1)
  let p := MvPowerSeries.truncTotal m f
  have he := hm f p.toMvPowerSeries
    (Lax208278Proofs.ContinuousDerivations.trunc_agree f le_rfl) I (Nat.lt_succ_self _)
  rw [he]
  change weight (φ p.toMvPowerSeries) r I ≤ _
  refine (polynomial_weight_bound φ hr.le hρ.le hb p I).trans ?_
  have hcoeff : ∀ J, |MvPolynomial.coeff J p| ≤ |MvPowerSeries.coeff J f| := by
    intro J
    simp only [p, MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs
    · exact le_rfl
    · simpa only [abs_zero] using abs_nonneg (MvPowerSeries.coeff J f)
  calc
    _ ≤ ∑ J ∈ p.support, weight f ρ J := Finset.sum_le_sum fun J _ =>
      mul_le_mul_of_nonneg_right (hcoeff J) (pow_nonneg hρ.le _)
    _ ≤ mass f ρ := hs.sum_le_tsum _ (fun J _ => weight_nonnegative f hρ.le J)
    _ ≤ _ := by linarith

end Lax825748Proofs.Composition
