import Lax825748Proofs.Vanishing

noncomputable section

namespace Lax825748Proofs.TensorEvaluation

open Lax825748.Series Lax825748.ShuffleIdentities
open ShuffleTensor
open scoped BigOperators

def tailWord {X : Type} {p : ℕ} : (Fin p → Word X) →* (Fin (p + 1) → Word X) where
  toFun v := Fin.cons 1 v
  map_one' := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  map_mul' u v := by ext i; exact Fin.cases rfl (fun _ => rfl) i

def tailHom {X : Type} (p : ℕ) : TensorPolynomial X p →ₐ[ℝ] TensorPolynomial X (p + 1) :=
  MonoidAlgebra.lift ℝ (TensorPolynomial X (p + 1)) (Fin p → Word X)
    ((MonoidAlgebra.of ℝ _).comp tailWord)

@[simp] theorem tail_single {X : Type} {p : ℕ} (v : Fin p → Word X) (a : ℝ) :
    tailHom p (MonoidAlgebra.single v a) = MonoidAlgebra.single (Fin.cons 1 v) a := by
  simp [tailHom, tailWord, MonoidAlgebra.of_apply]

theorem tail_slot {X : Type} {p : ℕ} (i : Fin p) (P : NCPolynomial X) :
    tailHom p (Coproduct.slotHom i P) = Coproduct.slotHom i.succ P := by
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    change tailHom p (Coproduct.slotHom i (MonoidAlgebra.single w 1)) =
      Coproduct.slotHom i.succ (MonoidAlgebra.single w 1)
    simp only [Coproduct.slotHom_single, tail_single]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Coproduct.slotWord, Ne.symm (Fin.succ_ne_zero i)]
    · simp [Coproduct.slotWord]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | smul a P hP => simp only [map_smul, hP]

theorem head_tail_eval {X : Type} {p : ℕ} (S : Fin (p + 1) → NCSeries X)
    (P : NCPolynomial X) (B : TensorPolynomial X p) :
    tensorPairingLinear S (Coproduct.slotHom 0 P * tailHom p B) =
      pairing (S 0) P * tensorPairingLinear (fun i => S i.succ) B := by
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    induction B using MonoidAlgebra.induction_on with
    | of v =>
      change tensorPairingLinear S
        (Coproduct.slotHom 0 (MonoidAlgebra.single w 1) * tailHom p (MonoidAlgebra.single v 1)) =
          pairing (S 0) (MonoidAlgebra.single w 1) *
            tensorPairingLinear (fun i => S i.succ) (MonoidAlgebra.single v 1)
      simp [Coproduct.slotHom_single, MonoidAlgebra.single_mul_single, Fin.prod_univ_succ,
        Coproduct.slotWord]
    | add B C hB hC => simp only [map_add, mul_add, hB, hC]
    | smul a B hB =>
      simp only [map_smul, mul_smul_comm, hB, smul_eq_mul]
      ring
  | add P Q hP hQ => simp only [map_add, add_mul, Series.pairing_add, hP, hQ]
  | smul a P hP =>
    simp only [map_smul, smul_mul_assoc, hP, Series.pairing_smul, smul_eq_mul]
    ring

def tensorMonomial {X : Type} {p : ℕ} (P : Fin p → NCPolynomial X) : TensorPolynomial X p :=
  (List.ofFn fun i => Coproduct.slotHom i (P i)).prod

theorem tensorMonomial_succ {X : Type} {p : ℕ} (P : Fin (p + 1) → NCPolynomial X) :
    tensorMonomial P = Coproduct.slotHom 0 (P 0) *
      tailHom p (tensorMonomial fun i => P i.succ) := by
  unfold tensorMonomial
  rw [List.ofFn_succ, List.prod_cons, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, tail_slot]

theorem tensorMonomial_eval {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (P : Fin p → NCPolynomial X) : tensorPairingLinear S (tensorMonomial P) =
      ∏ i, pairing (S i) (P i) := by
  induction p with
  | zero => simp [tensorMonomial, tensorPairingLinear, MonoidAlgebra.one_def]
  | succ p ih => rw [tensorMonomial_succ, head_tail_eval, ih, Fin.prod_univ_succ]

def reindexWord {X : Type} {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    (Fin p → Word X) →* (Fin p → Word X) where
  toFun v := fun i => v (σ.symm i)
  map_one' := rfl
  map_mul' _ _ := rfl

def reindexHom {X : Type} {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    TensorPolynomial X p →ₐ[ℝ] TensorPolynomial X p :=
  MonoidAlgebra.lift ℝ (TensorPolynomial X p) (Fin p → Word X)
    ((MonoidAlgebra.of ℝ _).comp (reindexWord σ))

@[simp] theorem reindex_single {X : Type} {p : ℕ} (σ : Equiv.Perm (Fin p))
    (v : Fin p → Word X) (a : ℝ) : reindexHom σ (MonoidAlgebra.single v a) =
      MonoidAlgebra.single (fun i => v (σ.symm i)) a := by
  simp [reindexHom, reindexWord, MonoidAlgebra.of_apply]

theorem reindex_slot {X : Type} {p : ℕ} (σ : Equiv.Perm (Fin p)) (i : Fin p)
    (P : NCPolynomial X) : reindexHom σ (Coproduct.slotHom i P) = Coproduct.slotHom (σ i) P := by
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    change reindexHom σ (Coproduct.slotHom i (MonoidAlgebra.single w 1)) =
      Coproduct.slotHom (σ i) (MonoidAlgebra.single w 1)
    simp only [Coproduct.slotHom_single, reindex_single]
    congr 1
    funext j
    by_cases h : j = σ i
    · subst j; simp [Coproduct.slotWord]
    · have hj : σ.symm j ≠ i := by intro hj; apply h; simpa using congrArg σ hj
      simp [Coproduct.slotWord, h, hj]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | smul a P hP => simp only [map_smul, hP]

theorem reindex_eval {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (σ : Equiv.Perm (Fin p)) (B : TensorPolynomial X p) :
    tensorPairingLinear S (reindexHom σ B) = tensorPairingLinear (fun i => S (σ i)) B := by
  induction B using MonoidAlgebra.induction_on with
  | of v =>
    change tensorPairingLinear S (reindexHom σ (MonoidAlgebra.single v 1)) =
      tensorPairingLinear (fun i => S (σ i)) (MonoidAlgebra.single v 1)
    rw [reindex_single, tensor_single, tensor_single, one_mul, one_mul]
    exact (Fintype.prod_equiv σ (fun i => S (σ i) (v i))
      (fun i => S i (v (σ.symm i))) (by intro i; simp)).symm
  | add B C hB hC => simp only [map_add, hB, hC]
  | smul a B hB => simp only [map_smul, hB]

theorem permutation_tensor_eval {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (σ : Equiv.Perm (Fin p)) (P : Fin p → NCPolynomial X) :
    tensorPairingLinear S ((List.ofFn fun i => Coproduct.slotHom (σ i) (P i)).prod) =
      ∏ i, pairing (S (σ i)) (P i) := by
  have he : reindexHom σ (tensorMonomial P) =
      (List.ofFn fun i => Coproduct.slotHom (σ i) (P i)).prod := by
    simp [tensorMonomial, map_list_prod, List.map_ofFn, Function.comp_def, reindex_slot]
  rw [← he, reindex_eval, tensorMonomial_eval]

end Lax825748Proofs.TensorEvaluation
