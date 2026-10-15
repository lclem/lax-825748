import Lax825748.FactorialEstimate
import Lax825748Proofs.Majorants
import Lax208278Proofs.RepresentationMap

noncomputable section

namespace Lax825748Proofs.WordMajorant

open Lax208278.Series Lax208278.FormalSeries Lax208278.DifferentialRepresentation
open Lax825748.ConvergentSeries
open Majorants
open scoped BigOperators

theorem field_bound {d : ℕ} {α B C : ℝ} (_hα : 0 ≤ α) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (A : VectorField d) (hA : ∀ i, HasGeometricBound (A i) α C)
    (f : StateSeries d) (k : ℕ) (hf : Bounds f (B • geometric d C ^ (k + 1))) :
    Bounds (applyVectorField A f)
      (((d : ℝ) * α * B * ((k : ℝ) + 1) * C) • geometric d C ^ (k + 3)) := by
  have hi : ∀ i, Bounds (A i * MvPowerSeries.pderiv ℝ i f)
      ((α * B * ((k : ℝ) + 1) * C) • geometric d C ^ (k + 3)) := by
    intro i
    have ha : Bounds (A i) (α • geometric d C) := by
      intro I
      simpa only [MvPowerSeries.coeff_smul, coeff_geometric] using hA i I
    have hd : Bounds (MvPowerSeries.pderiv ℝ i f)
        ((B * (((k : ℝ) + 1) * C)) • geometric d C ^ (k + 2)) := by
      have hh := (hf.derivative i).trans
        (by simpa only [Derivation.map_smul, smul_smul, Nat.cast_add, Nat.cast_one] using
          (geometric_pow_derivative hC i k).smul hB)
      exact hh
    have hh := ha.mul hd
    convert hh using 1
    simp only [smul_mul_smul_comm]
    rw [show geometric d C * geometric d C ^ (k + 2) = geometric d C ^ (k + 3) by
      rw [← pow_succ']]
    congr 1
    ring
  intro I
  simp only [applyVectorField, map_sum, MvPowerSeries.coeff_smul]
  calc
    _ ≤ ∑ i, |MvPowerSeries.coeff I (A i * MvPowerSeries.pderiv ℝ i f)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, MvPowerSeries.coeff I
        ((α * B * ((k : ℝ) + 1) * C) • geometric d C ^ (k + 3)) :=
      Finset.sum_le_sum fun i _ => hi i I
    _ = _ := by simp; ring

def amplitude (d : ℕ) (α C : ℝ) (p : ℕ) : ℝ :=
  α * (2 * (d : ℝ) * α * C) ^ p * (p.factorial : ℝ)

theorem amplitude_nonnegative (d : ℕ) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (p : ℕ) :
    0 ≤ amplitude d α C p := by unfold amplitude; positivity

theorem amplitude_step (d : ℕ) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (p : ℕ) :
    (d : ℝ) * α * amplitude d α C p * ((2 * p : ℕ) + 1) * C ≤
      amplitude d α C (p + 1) := by
  have hb := amplitude_nonnegative d hα hC p
  have he : amplitude d α C (p + 1) =
      ((d : ℝ) * α * amplitude d α C p * C) * (2 * ((p : ℝ) + 1)) := by
    simp only [amplitude, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  push_cast
  have hh : 0 ≤ (d : ℝ) * α * amplitude d α C p * C := by positivity
  nlinarith

theorem act_bound {X : Type} {d : ℕ} (R : Representation X d) {α C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hh : HasGeometricBound R.output α C)
    (hA : ∀ x i, HasGeometricBound (R.fields x i) α C) (l : List X) :
    Bounds (act R R.output (FreeMonoid.ofList l))
      (amplitude d α C l.length • geometric d C ^ (2 * l.length + 1)) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro I
    simpa [amplitude, MvPowerSeries.coeff_smul] using hh I
  | append_singleton l x ih =>
    have hs := field_bound hα (amplitude_nonnegative d hα hC l.length) hC
      (R.fields x) (hA x) _ (2 * l.length) ih
    have hb : Bounds (applyVectorField (R.fields x) (act R R.output (FreeMonoid.ofList l)))
        (amplitude d α C (l.length + 1) • geometric d C ^ (2 * l.length + 3)) := by
      apply hs.mono
      intro I
      simp only [MvPowerSeries.coeff_smul]
      apply mul_le_mul_of_nonneg_right (amplitude_step d hα hC l.length)
      exact (geometric_nonnegative d hC).pow _ I
    convert hb using 1
    · exact Lax208278Proofs.RepresentationMap.act_mul R R.output
        (FreeMonoid.ofList l) (FreeMonoid.of x)
    · simp only [List.length_append, List.length_singleton]
      congr 2

/--
---
conclusion: Lax825748.FactorialEstimate.word_majorant
---
Use the nonnegative series $F_I=C^{|I|}$ as a coefficient majorant.
Its derivatives satisfy $\partial_i F\preceq C F^2$. After $p$ vector
fields the majorant is $\alpha(2d\alpha C)^p p! F^{2p+1}$; its constant
coefficient is the claimed bound.
-/
theorem word_majorant {X : Type} {d : ℕ} (R : Representation X d)
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C)
    (hh : HasGeometricBound R.output α C)
    (hA : ∀ x i, HasGeometricBound (R.fields x i) α C) (w : Word X) :
    |generatingSeries R w| ≤
      α * (2 * (d : ℝ) * α * C) ^ w.toList.length * (w.toList.length.factorial : ℝ) := by
  have hb := act_bound R hα.le hC.le hh hA w.toList 0
  have hzero : MvPowerSeries.constantCoeff (geometric d C) = 1 := by
    change C ^ Lax208278.Monomials.totalDegree (0 : Fin d →₀ ℕ) = 1
    simp [Lax208278.Monomials.totalDegree]
  simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.constantCoeff_smul,
    map_pow, hzero, one_pow, smul_eq_mul, mul_one, amplitude,
    FreeMonoid.ofList_toList, generatingSeries] using hb

end Lax825748Proofs.WordMajorant
