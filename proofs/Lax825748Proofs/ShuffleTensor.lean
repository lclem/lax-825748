import Lax825748Proofs.Coproduct
import Lax825748Proofs.Shuffle

noncomputable section

namespace Lax825748Proofs.ShuffleTensor

open Lax825748.Series Lax825748.Shuffle Lax825748.ShuffleIdentities
open scoped BigOperators

theorem shuffle_sum_right {X ι : Type} (s : Finset ι) (S : NCSeries X)
    (T : ι → NCSeries X) :
    shuffle S (∑ i ∈ s, T i) = ∑ i ∈ s, shuffle S (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Shuffle.commutative, Shuffle.shuffle_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Shuffle.shuffle_add_right, ih]

theorem shuffle_family_succ {X : Type} {p : ℕ} (S : Fin (p + 1) → NCSeries X) :
    shuffleList (List.ofFn S) = shuffle (S 0) (shuffleList (List.ofFn fun i => S i.succ)) := by
  rw [List.ofFn_succ, shuffleList]

theorem family_update_zero {X : Type} {p : ℕ} (S : Fin (p + 1) → NCSeries X)
    (T : NCSeries X) :
    shuffleList (List.ofFn (Function.update S 0 T)) =
      shuffle T (shuffleList (List.ofFn fun i => S i.succ)) := by
  rw [shuffle_family_succ]
  simp

theorem family_update_succ {X : Type} {p : ℕ} (S : Fin (p + 1) → NCSeries X)
    (j : Fin p) (T : NCSeries X) :
    shuffleList (List.ofFn (Function.update S j.succ T)) =
      shuffle (S 0) (shuffleList (List.ofFn (Function.update (fun i => S i.succ) j T))) := by
  rw [shuffle_family_succ]
  have htail : (fun i => Function.update S j.succ T i.succ) =
      Function.update (fun i => S i.succ) j T := by
    funext i
    by_cases h : i = j <;> simp [h]
  rw [htail]
  rfl

theorem shuffle_family_shift {X : Type} (x : X) {p : ℕ} (S : Fin p → NCSeries X) :
    Shuffle.shift x (shuffleList (List.ofFn S)) =
      ∑ i, shuffleList (List.ofFn (Function.update S i (Shuffle.shift x (S i)))) := by
  induction p with
  | zero => simp [shuffleList, Shuffle.shift_constant]
  | succ p ih =>
    rw [shuffle_family_succ, Shuffle.shift_shuffle, ih, shuffle_sum_right, Fin.sum_univ_succ]
    rw [family_update_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [family_update_succ]

theorem shuffle_family_empty {X : Type} {p : ℕ} (S : Fin p → NCSeries X) :
    shuffleList (List.ofFn S) 1 = ∏ i, S i 1 := by
  induction p with
  | zero => simp [shuffleList, constantSeries]
  | succ p ih => rw [shuffle_family_succ, Shuffle.shuffle_empty, ih, Fin.prod_univ_succ]

def tensorPairingLinear {X : Type} {p : ℕ} (S : Fin p → NCSeries X) :
    TensorPolynomial X p →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (fun v => ∏ i, S i (v i))).comp
    (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem tensor_single {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (v : Fin p → Word X) (a : ℝ) :
    tensorPairingLinear S (MonoidAlgebra.single v a) = a * ∏ i, S i (v i) := by
  simp [tensorPairingLinear]

theorem tensor_distributed {X : Type} {p : ℕ} (S : Fin p → NCSeries X) (w : Word X) :
    tensorPairingLinear S (Coproduct.distributedWord p w) =
      ((distributions p w.toList).map fun v => ∏ i, S i (FreeMonoid.ofList (v i))).sum := by
  simp [Coproduct.distributedWord, map_list_sum, List.map_map, Function.comp_def]

theorem tensor_distributed_cons {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (x : X) (w : Word X) :
    tensorPairingLinear S (Coproduct.distributedWord p (FreeMonoid.of x * w)) =
      ∑ i, tensorPairingLinear (Function.update S i (Shuffle.shift x (S i)))
        (Coproduct.distributedWord p w) := by
  simp only [tensor_distributed, FreeMonoid.toList_of_mul, distributions,
    Coproduct.sum_flatMap_map, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
  rw [Coproduct.list_sum_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply List.map_congr_left
  intro v _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i <;> simp [h, Shuffle.shift]

theorem pairing_family_word {X : Type} {p : ℕ} (S : Fin p → NCSeries X) (w : Word X) :
    shuffleList (List.ofFn S) w = tensorPairingLinear S (Coproduct.distributedWord p w) := by
  induction w using FreeMonoid.recOn generalizing S with
  | one =>
    rw [shuffle_family_empty, tensor_distributed]
    simp [distributions]
  | of_mul x w ih =>
    change Shuffle.shift x (shuffleList (List.ofFn S)) w = _
    rw [shuffle_family_shift, tensor_distributed_cons]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact ih _

/--
---
conclusion: Lax825748.ShuffleIdentities.pairing_coproduct
---
-/
theorem pairing_coproduct {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (P : NCPolynomial X) :
    pairing (shuffleList (List.ofFn S)) P = tensorPairing S (coproduct p P) := by
  change _ = tensorPairingLinear S (coproduct p P)
  rw [Coproduct.coproduct_eq_hom]
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    change pairing (shuffleList (List.ofFn S)) (wordPolynomial w) =
      tensorPairingLinear S (Coproduct.coproductHom p (wordPolynomial w))
    rw [Series.pairing_word]
    have hc : Coproduct.coproductHom p (wordPolynomial w) = Coproduct.distributedWord p w := by
      rw [Coproduct.distributed_eq]
      simp [Coproduct.coproductHom, wordPolynomial]
    rw [hc]
    exact pairing_family_word S w
  | add P Q hP hQ => simp only [Series.pairing_add, map_add, hP, hQ]
  | smul a P hP => simp only [Series.pairing_smul, map_smul, hP, smul_eq_mul]

end Lax825748Proofs.ShuffleTensor
