import Lax825748Proofs.WeightedMass
import Mathlib.RingTheory.MvPowerSeries.PiTopology

noncomputable section

namespace Lax825748Proofs.Reciprocal

open Lax825748.FormalSeries Lax825748.Monomials Lax825748.ConvergentSeries
open WeightedMass PowerSeriesBounds MvPowerSeries.WithPiTopology
open scoped BigOperators MvPowerSeries.WithPiTopology

theorem geometric_sum_convergent {d : ℕ} (h : StateSeries d) (hh : Convergent h)
    (h0 : MvPowerSeries.constantCoeff h = 0) : Convergent (∑' n : ℕ, h ^ n) := by
  obtain ⟨r, hr, hb⟩ := common_small_radius (fun _ : Unit => h)
    (fun _ => hh) (fun _ => h0) (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨hs, hm⟩ := hb ()
  have hm0 : 0 ≤ mass h r := mass_nonnegative h hr.le
  have hm1 : mass h r < 1 := by linarith
  have hgeom := summable_geometric_of_lt_one hm0 hm1
  have hsum : (∑' n : ℕ, mass h r ^ n) ≤ 2 := by
    rw [tsum_geometric_of_lt_one hm0 hm1]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  refine ⟨2, by norm_num, r⁻¹, inv_pos.mpr hr, ?_⟩
  intro I
  rw [inv_pow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  have hterm : ∀ n : ℕ, ‖MvPowerSeries.coeff I (h ^ n) * r ^ totalDegree I‖ ≤ mass h r ^ n := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
    exact (weight_le_mass hr.le (hs.pow hr.le n) I).trans (mass_pow_le hs hr.le n)
  have hnorm : Summable (fun n : ℕ => ‖MvPowerSeries.coeff I (h ^ n) * r ^ totalDegree I‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgeom
  have hc := (hasSum_iff_hasSum_coeff.mp (summable_pow_of_constantCoeff_eq_zero h0).hasSum) I
  have he := (hc.mul_right (r ^ totalDegree I)).tsum_eq
  calc
    _ = ‖MvPowerSeries.coeff I (∑' n : ℕ, h ^ n) * r ^ totalDegree I‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
    _ = ‖∑' n : ℕ, MvPowerSeries.coeff I (h ^ n) * r ^ totalDegree I‖ := congrArg norm he.symm
    _ ≤ ∑' n : ℕ, ‖MvPowerSeries.coeff I (h ^ n) * r ^ totalDegree I‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, mass h r ^ n := hnorm.tsum_le_tsum hterm hgeom
    _ ≤ 2 := hsum

theorem convergent_inverse {d : ℕ} (f : StateSeries d) (hf : Convergent f)
    (h0 : MvPowerSeries.constantCoeff f ≠ 0) : Convergent f⁻¹ := by
  let c := MvPowerSeries.constantCoeff f
  let h : StateSeries d := 1 - c⁻¹ • f
  have hh : Convergent h := by
    change Convergent (1 + -(c⁻¹ • f))
    apply convergent_add (by simpa using convergent_C (d := d) 1)
    simpa only [neg_one_smul] using convergent_smul (-1) (convergent_smul c⁻¹ hf)
  have hz : MvPowerSeries.constantCoeff h = 0 := by
    simp [h, c, h0]
  let g : StateSeries d := ∑' n : ℕ, h ^ n
  have hg : Convergent g := geometric_sum_convergent h hh hz
  have he : (c⁻¹ • g) * f = 1 := by
    have hhg := tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hz
    change g * (1 - h) = 1 at hhg
    simpa only [h, sub_sub_cancel, mul_smul_comm, smul_mul_assoc] using hhg
  have heq : c⁻¹ • g = f⁻¹ := by
    calc
      _ = (c⁻¹ • g) * (f * f⁻¹) := by rw [MvPowerSeries.mul_inv_cancel f h0, mul_one]
      _ = f⁻¹ := by rw [← mul_assoc, he, one_mul]
  rw [← heq]
  exact convergent_smul _ hg

end Lax825748Proofs.Reciprocal
