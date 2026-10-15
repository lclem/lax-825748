import Lax825748.Series
import Mathlib.Tactic

noncomputable section

namespace Lax825748Proofs.Series

open Lax825748.Series

def pairingLinear {X : Type} (S : NCSeries X) : NCPolynomial X →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ S).comp (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

theorem pairingLinear_apply {X : Type} (S : NCSeries X) (P : NCPolynomial X) :
    pairingLinear S P = pairing S P := rfl

@[simp] theorem pairing_single {X : Type} (S : NCSeries X) (w : Word X) (a : ℝ) :
    pairing S (MonoidAlgebra.single w a) = a * S w := by
  simp [pairing]

@[simp] theorem pairing_word {X : Type} (S : NCSeries X) (w : Word X) :
    pairing S (wordPolynomial w) = S w := by
  simp [wordPolynomial]

@[simp] theorem pairing_zero {X : Type} (S : NCSeries X) : pairing S 0 = 0 := by
  exact (pairingLinear S).map_zero

@[simp] theorem pairing_add {X : Type} (S : NCSeries X) (P Q : NCPolynomial X) :
    pairing S (P + Q) = pairing S P + pairing S Q :=
  (pairingLinear S).map_add P Q

@[simp] theorem pairing_smul {X : Type} (S : NCSeries X) (a : ℝ) (P : NCPolynomial X) :
    pairing S (a • P) = a * pairing S P :=
  (pairingLinear S).map_smul a P

@[simp] theorem pairing_add_series {X : Type} (S T : NCSeries X) (P : NCPolynomial X) :
    pairing (S + T) P = pairing S P + pairing T P := by
  simp [pairing, mul_add, Finsupp.sum_add]

@[simp] theorem pairing_smul_series {X : Type} (a : ℝ) (S : NCSeries X)
    (P : NCPolynomial X) : pairing (a • S) P = a * pairing S P := by
  simp [pairing, Finsupp.mul_sum, mul_left_comm]

@[simp] theorem word_mul {X : Type} (u v : Word X) :
    wordPolynomial (u * v) = wordPolynomial u * wordPolynomial v := by
  simp [wordPolynomial, MonoidAlgebra.single_mul_single]

theorem pairing_mul {X : Type} (S : NCSeries X) (P Q : NCPolynomial X) :
    pairing S (P * Q) = P.coeff.sum fun u a =>
      Q.coeff.sum fun v b => a * b * S (u * v) := by
  simp [pairing, MonoidAlgebra.mul_def, Finsupp.sum_sum_index,
    add_mul]

theorem pairing_mul_word {X : Type} (S : NCSeries X) (P : NCPolynomial X)
    (w : Word X) : pairing S (P * wordPolynomial w) =
      P.coeff.sum fun u a => a * S (u * w) := by
  rw [pairing_mul]
  simp [wordPolynomial]

theorem pairing_word_mul {X : Type} (S : NCSeries X) (w : Word X)
    (P : NCPolynomial X) : pairing S (wordPolynomial w * P) =
      P.coeff.sum fun u a => a * S (w * u) := by
  rw [pairing_mul]
  simp [wordPolynomial]

theorem pairing_right_residual {X : Type} (S : NCSeries X) (P Q : NCPolynomial X) :
    pairing (rightResidual S P) Q = pairing S (P * Q) := by
  change Q.coeff.sum (fun v b => b * pairing S (P * wordPolynomial v)) = _
  simp_rw [pairing_mul_word, Finsupp.mul_sum]
  rw [pairing_mul, Finsupp.sum_comm]
  congr 1
  funext v b
  congr 1
  funext u a
  ring

theorem pairing_left_residual {X : Type} (S : NCSeries X) (P Q : NCPolynomial X) :
    pairing (leftResidual P S) Q = pairing S (Q * P) := by
  change Q.coeff.sum (fun v b => b * pairing S (wordPolynomial v * P)) = _
  simp_rw [pairing_word_mul, Finsupp.mul_sum]
  rw [pairing_mul]
  congr 1
  funext v b
  congr 1
  funext u a
  ring

@[simp] theorem right_residual_word {X : Type} (S : NCSeries X) (u v : Word X) :
    rightResidual S (wordPolynomial u) v = S (u * v) := by
  simp [rightResidual, ← word_mul]

theorem residual_mul {X : Type} (S : NCSeries X) (P Q : NCPolynomial X) :
    rightResidual (rightResidual S P) Q = rightResidual S (P * Q) := by
  funext w
  simp [rightResidual, pairing_right_residual, mul_assoc]

end Lax825748Proofs.Series
