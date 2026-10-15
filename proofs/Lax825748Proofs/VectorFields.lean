import Lax825748Proofs.RepresentationMap

noncomputable section

namespace Lax825748Proofs.VectorFields

open Lax825748.FormalSeries
open RepresentationMap
open scoped BigOperators

theorem pderiv_comm {d : ℕ} (i j : Fin d) (f : StateSeries d) :
    MvPowerSeries.pderiv ℝ i (MvPowerSeries.pderiv ℝ j f) =
      MvPowerSeries.pderiv ℝ j (MvPowerSeries.pderiv ℝ i f) := by
  by_cases h : i = j
  · subst j; rfl
  · ext I
    simp only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply]
    simp only [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h),
      add_zero]
    rw [show I + Finsupp.single i 1 + Finsupp.single j 1 =
      I + Finsupp.single j 1 + Finsupp.single i 1 by ac_rfl]
    ring

def bracket {d : ℕ} (A B : VectorField d) : VectorField d :=
  fun i => applyVectorField B (A i) - applyVectorField A (B i)

theorem field_sum {d : ℕ} {ι : Type} (s : Finset ι) (A : VectorField d)
    (f : ι → StateSeries d) :
    applyVectorField A (∑ i ∈ s, f i) = ∑ i ∈ s, applyVectorField A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, field_add, ih]

theorem field_bracket {d : ℕ} (A B : VectorField d) (f : StateSeries d) :
    applyVectorField (bracket A B) f =
      applyVectorField B (applyVectorField A f) -
        applyVectorField A (applyVectorField B f) := by
  have exp (A B : VectorField d) :
      applyVectorField B (applyVectorField A f) =
        (∑ i, applyVectorField B (A i) * MvPowerSeries.pderiv ℝ i f) +
        ∑ i, ∑ j, A i * B j *
          MvPowerSeries.pderiv ℝ j (MvPowerSeries.pderiv ℝ i f) := by
    change applyVectorField B (∑ i, A i * MvPowerSeries.pderiv ℝ i f) = _
    rw [field_sum]
    simp only [field_mul, Finset.sum_add_distrib]
    congr 1
    simp only [applyVectorField, Finset.mul_sum, mul_assoc]
  have hsecond :
      (∑ i, ∑ j, A i * B j * MvPowerSeries.pderiv ℝ j (MvPowerSeries.pderiv ℝ i f)) =
        ∑ i, ∑ j, B i * A j * MvPowerSeries.pderiv ℝ j (MvPowerSeries.pderiv ℝ i f) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [pderiv_comm]
    ring
  rw [exp, exp, ← hsecond]
  simp only [applyVectorField, bracket, sub_mul, Finset.sum_sub_distrib]
  abel

end Lax825748Proofs.VectorFields
