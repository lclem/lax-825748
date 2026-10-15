import Lax825748Proofs.VectorFields

noncomputable section

namespace Lax825748Proofs.Operators

open Lax825748.Series Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.LieRank RepresentationMap

def actLinear {X : Type} {d : ℕ} (R : Representation X d) (w : Word X) :
    StateSeries d →ₗ[ℝ] StateSeries d where
  toFun f := act R f w
  map_add' := act_add R w
  map_smul' := act_smul R w

def operator {X : Type} {d : ℕ} (R : Representation X d) :
    NCPolynomial X →ₗ[ℝ] Module.End ℝ (StateSeries d) :=
  (Finsupp.linearCombination ℝ (actLinear R)).comp
    (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem operator_word {X : Type} {d : ℕ} (R : Representation X d) (w : Word X) :
    operator R (wordPolynomial w) = actLinear R w := by
  simp [operator, wordPolynomial]

theorem operator_mul {X : Type} {d : ℕ} (R : Representation X d) (P Q : NCPolynomial X) :
    operator R (P * Q) = operator R Q * operator R P := by
  induction P using MonoidAlgebra.induction_on with
  | of u =>
    change operator R (wordPolynomial u * Q) = operator R Q * operator R (wordPolynomial u)
    induction Q using MonoidAlgebra.induction_on with
    | of v =>
      change operator R (wordPolynomial u * wordPolynomial v) =
        operator R (wordPolynomial v) * operator R (wordPolynomial u)
      rw [← Series.word_mul, operator_word, operator_word, operator_word]
      apply LinearMap.ext
      intro f
      exact act_mul R f u v
    | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ, add_mul]
    | smul a P hP => simp only [mul_smul_comm, map_smul, hP, smul_mul_assoc]
  | add P Q hP hQ => simp only [add_mul, map_add, hP, hQ, mul_add]
  | smul a P hP => simp only [smul_mul_assoc, map_smul, hP, mul_smul_comm]

theorem field_coeff_add {d : ℕ} (A B : VectorField d) (f : StateSeries d) :
    applyVectorField (A + B) f = applyVectorField A f + applyVectorField B f := by
  simp [applyVectorField, add_mul, Finset.sum_add_distrib]

theorem field_coeff_smul {d : ℕ} (a : ℝ) (A : VectorField d) (f : StateSeries d) :
    applyVectorField (a • A) f = a • applyVectorField A f := by
  simp [applyVectorField, Finset.smul_sum]

theorem lie_operator_field {X : Type} {d : ℕ} (R : Representation X d)
    (P : LiePolynomial X) :
    ∃ A : VectorField d, ∀ f, operator R P.val f = applyVectorField A f := by
  apply LieSubalgebra.lieSpan_induction ℝ (x := P.val) (s := Set.range letter)
    (p := fun P _ => ∃ A : VectorField d, ∀ f, operator R P f = applyVectorField A f)
    ?_ ?_ ?_ ?_ ?_ P.property
  · rintro _ ⟨x, rfl⟩
    refine ⟨R.fields x, ?_⟩
    intro f
    rw [letter, operator_word]
    rfl
  · refine ⟨0, ?_⟩
    intro f
    simp [applyVectorField]
  · intro P Q _ _ hP hQ
    obtain ⟨A, hA⟩ := hP
    obtain ⟨B, hB⟩ := hQ
    refine ⟨A + B, ?_⟩
    intro f
    simp only [map_add, LinearMap.add_apply, hA, hB, field_coeff_add]
  · intro a P _ hP
    obtain ⟨A, hA⟩ := hP
    refine ⟨a • A, ?_⟩
    intro f
    simp only [map_smul, LinearMap.smul_apply, hA, field_coeff_smul]
  · intro P Q _ _ hP hQ
    obtain ⟨A, hA⟩ := hP
    obtain ⟨B, hB⟩ := hQ
    refine ⟨VectorFields.bracket A B, ?_⟩
    intro f
    rw [LieRing.of_associative_ring_bracket, map_sub, operator_mul, operator_mul]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hA, hB, VectorFields.field_bracket]

end Lax825748Proofs.Operators
