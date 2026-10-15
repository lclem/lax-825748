import Lax825748.Annihilator
import Lax825748Proofs.Series
import Lax825748Proofs.ShuffleTensor

noncomputable section

namespace Lax825748Proofs.Annihilator

open Lax825748.Series Lax825748.Annihilator
open Lax825748.Shuffle Lax825748.ShuffleIdentities
open scoped BigOperators

/--
---
conclusion: Lax825748.Annihilator.closed_residual
---
The defining ideal is a left ideal, so its annihilator is invariant under
right residuals.
-/
theorem closed_residual {X : Type} (K : LieSubalgebraOfPolynomials X)
    (S : NCSeries X) (hS : InAnnihilator K S) (P : NCPolynomial X) :
    InAnnihilator K (rightResidual S P) := by
  intro Q hQ
  rw [Series.pairing_right_residual]
  exact hS (P * Q) ((generatedIdeal K).mul_mem_left P hQ)

theorem tensor_slot_right {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (v : Fin p → Word X) (i : Fin p) (P : NCPolynomial X) :
    ShuffleTensor.tensorPairingLinear S (MonoidAlgebra.single v 1 * Coproduct.slotHom i P) =
      pairing (S i) (wordPolynomial (v i) * P) * ∏ j ∈ Finset.univ.erase i, S j (v j) := by
  induction P using MonoidAlgebra.induction_on with
  | of u =>
    change ShuffleTensor.tensorPairingLinear S
      (MonoidAlgebra.single v 1 * Coproduct.slotHom i (wordPolynomial u)) =
      pairing (S i) (wordPolynomial (v i) * wordPolynomial u) * _
    simp only [wordPolynomial, Coproduct.slotHom_single, MonoidAlgebra.single_mul_single,
      one_mul, ShuffleTensor.tensor_single, Series.pairing_single]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => S j ((v * Coproduct.slotWord i u) j))
      (Finset.mem_univ i)]
    simp only [Pi.mul_apply, Coproduct.slotWord]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, Series.pairing_add, hP, hQ, add_mul]
  | smul a P hP =>
    simp only [map_smul, mul_smul_comm, Series.pairing_smul, hP, smul_eq_mul]
    ring

theorem tensor_kill_right {X : Type} {p : ℕ} (K : LieSubalgebraOfPolynomials X)
    (S : Fin p → NCSeries X) (i : Fin p) (hS : InAnnihilator K (S i))
    (P : NCPolynomial X) (hP : P ∈ generatedIdeal K) (B : TensorPolynomial X p) :
    ShuffleTensor.tensorPairingLinear S (B * Coproduct.slotHom i P) = 0 := by
  induction B using MonoidAlgebra.induction_on with
  | of v =>
    change ShuffleTensor.tensorPairingLinear S
      (MonoidAlgebra.single v 1 * Coproduct.slotHom i P) = 0
    rw [tensor_slot_right, hS _ ((generatedIdeal K).mul_mem_left _ hP), zero_mul]
  | add B C hB hC => simp only [add_mul, map_add, hB, hC, add_zero]
  | smul a B hB => simp only [smul_mul_assoc, map_smul, hB, smul_zero]

theorem annihilator_coproduct {X : Type} {p : ℕ} (K : LieSubalgebraOfPolynomials X)
    (S : Fin p → NCSeries X) (hS : ∀ i, InAnnihilator K (S i))
    (P : NCPolynomial X) (hP : P ∈ generatedIdeal K) :
    ∀ B : TensorPolynomial X p,
      ShuffleTensor.tensorPairingLinear S (B * coproduct p P) = 0 := by
  change P ∈ Submodule.span (NCPolynomial X) {P | ∃ k : K, P = k.val.val} at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨k, rfl⟩ := hP
    intro B
    rw [Lax825748.ShuffleIdentities.lie_primitive, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Coproduct.insertFactor_eq]
    exact tensor_kill_right K S i (hS i) k.val.val
      (Ideal.subset_span ⟨k, rfl⟩) B
  | zero =>
    intro B
    simp [Coproduct.coproduct_eq_hom]
  | add P Q _ _ hP hQ =>
    intro B
    simp only [Coproduct.coproduct_eq_hom, map_add, mul_add] at hP hQ ⊢
    rw [hP, hQ, add_zero]
  | smul A P _ hP =>
    intro B
    change ShuffleTensor.tensorPairingLinear S (B * coproduct p (A * P)) = 0
    rw [Lax825748.ShuffleIdentities.coproduct_multiplicative, ← mul_assoc]
    exact hP _

/--
---
conclusion: Lax825748.Annihilator.closed_shuffle
---
The coproduct of each generator of the defining left ideal is primitive;
every term therefore has a factor annihilated by one of the series.
-/
theorem closed_shuffle {X : Type} (K : LieSubalgebraOfPolynomials X)
    (S T : NCSeries X) (hS : InAnnihilator K S) (hT : InAnnihilator K T) :
    InAnnihilator K (shuffle S T) := by
  intro P hP
  let F : Fin 2 → NCSeries X := ![S, T]
  have hF : ∀ i, InAnnihilator K (F i) := by
    intro i
    fin_cases i
    · exact hS
    · exact hT
  have hh := annihilator_coproduct K F hF P hP 1
  rw [one_mul] at hh
  have hshuffle : shuffleList (List.ofFn F) = shuffle S T := by
    simp [F, List.ofFn_succ, shuffleList, Shuffle.commutative T (constantSeries 1),
      Shuffle.unit]
  rw [← hshuffle, Lax825748.ShuffleIdentities.pairing_coproduct]
  exact hh

end Lax825748Proofs.Annihilator
