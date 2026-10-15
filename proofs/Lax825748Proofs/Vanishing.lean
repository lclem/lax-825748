import Lax825748Proofs.ShuffleTensor

noncomputable section

namespace Lax825748Proofs.Vanishing

open Lax825748.Series Lax825748.LieRank Lax825748.Shuffle Lax825748.ShuffleIdentities
open scoped BigOperators

theorem ordered_product_sum {A : Type*} [Semiring A] {p j : ℕ}
    (F : Fin j → Fin p → A) :
    (List.ofFn fun k => ∑ i, F k i).prod =
      ∑ σ : Fin j → Fin p, (List.ofFn fun k => F k (σ k)).prod := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Finset.sum_mul]
    simp only [Finset.mul_sum]
    let e := Fin.consEquiv (fun _ : Fin (j + 1) => Fin p)
    have he := Fintype.sum_equiv e
      (fun v => F 0 v.1 * (List.ofFn fun k => F k.succ (v.2 k)).prod)
      (fun σ => (List.ofFn fun k => F k (σ k)).prod) (by
        intro v
        simp [e, List.ofFn_succ])
    simpa only [Fintype.sum_prod_type] using he

theorem coproduct_lie_product {X : Type} {j : ℕ} (p : ℕ) (Q : Fin j → LiePolynomial X) :
    coproduct p ((List.ofFn fun k => (Q k).val).prod) =
      ∑ σ : Fin j → Fin p, (List.ofFn fun k => Coproduct.slotHom (σ k) (Q k).val).prod := by
  rw [Coproduct.coproduct_eq_hom, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def]
  have hQ (k : Fin j) : Coproduct.coproductHom p (Q k).val =
      ∑ i : Fin p, Coproduct.slotHom i (Q k).val := by
    simpa only [Coproduct.coproduct_eq_hom, Coproduct.insertFactor_eq] using
      Lax825748.ShuffleIdentities.lie_primitive p (Q k)
  simp_rw [hQ]
  exact ordered_product_sum _

def eraseSlotWord {X : Type} {p : ℕ} (i : Fin p) :
    (Fin p → Word X) →* (Fin p → Word X) where
  toFun v := Function.update v i 1
  map_one' := by funext j; by_cases h : j = i <;> simp [h]
  map_mul' u v := by funext j; by_cases h : j = i <;> simp [h]

def eraseSlot {X : Type} {p : ℕ} (i : Fin p) : TensorPolynomial X p →ₐ[ℝ] TensorPolynomial X p :=
  MonoidAlgebra.lift ℝ (TensorPolynomial X p) (Fin p → Word X)
    ((MonoidAlgebra.of ℝ _).comp (eraseSlotWord i))

@[simp] theorem eraseSlot_single {X : Type} {p : ℕ} (i : Fin p) (v : Fin p → Word X) (a : ℝ) :
    eraseSlot i (MonoidAlgebra.single v a) = MonoidAlgebra.single (Function.update v i 1) a := by
  simp [eraseSlot, eraseSlotWord, MonoidAlgebra.of_apply]

theorem eraseSlot_slot {X : Type} {p : ℕ} (i k : Fin p) (h : i ≠ k) (P : NCPolynomial X) :
    eraseSlot i (Coproduct.slotHom k P) = Coproduct.slotHom k P := by
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    change eraseSlot i (Coproduct.slotHom k (MonoidAlgebra.single w 1)) =
      Coproduct.slotHom k (MonoidAlgebra.single w 1)
    rw [Coproduct.slotHom_single, eraseSlot_single]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j; simp [Coproduct.slotWord, h]
    · simp [hj]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | smul a P hP => simp only [map_smul, hP]

theorem tensor_eraseSlot_zero {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (i : Fin p) (hS : S i 1 = 0) (P : TensorPolynomial X p) :
    ShuffleTensor.tensorPairingLinear S (eraseSlot i P) = 0 := by
  induction P using MonoidAlgebra.induction_on with
  | of v =>
    change ShuffleTensor.tensorPairingLinear S (eraseSlot i (MonoidAlgebra.single v 1)) = 0
    rw [eraseSlot_single, ShuffleTensor.tensor_single, one_mul]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hS
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P hP => simp only [map_smul, hP, smul_zero]

theorem assignment_zero_of_not_surjective {X : Type} {p j : ℕ}
    (T : Fin p → NCSeries X) (hT : ∀ k, T k 1 = 0)
    (Q : Fin j → LiePolynomial X) (σ : Fin j → Fin p) (hns : ¬ Function.Surjective σ) :
    ShuffleTensor.tensorPairingLinear T
      ((List.ofFn fun k => Coproduct.slotHom (σ k) (Q k).val).prod) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin p, ∀ k, σ k ≠ i := by
    simpa only [Function.Surjective, not_forall, not_exists] using hns
  have hfixed : eraseSlot i ((List.ofFn fun k => Coproduct.slotHom (σ k) (Q k).val).prod) =
      (List.ofFn fun k => Coproduct.slotHom (σ k) (Q k).val).prod := by
    rw [map_list_prod]
    simp only [List.map_ofFn, Function.comp_def]
    congr 2
    funext k
    exact eraseSlot_slot i (σ k) (Ne.symm (hi k)) _
  rw [← hfixed]
  exact tensor_eraseSlot_zero T i (hT i) _

theorem assignment_zero {X : Type} {p j : ℕ} (hjp : j < p)
    (T : Fin p → NCSeries X) (hT : ∀ k, T k 1 = 0)
    (Q : Fin j → LiePolynomial X) (σ : Fin j → Fin p) :
    ShuffleTensor.tensorPairingLinear T
      ((List.ofFn fun k => Coproduct.slotHom (σ k) (Q k).val).prod) = 0 := by
  apply assignment_zero_of_not_surjective T hT Q σ
  intro hs
  have := Fintype.card_le_of_surjective σ hs
  simp only [Fintype.card_fin] at this
  omega

/--
---
conclusion: Lax825748.ShuffleIdentities.vanishing
---
In the coproduct expansion, fewer Lie factors than tensor slots leave an
empty slot in every term. A zero constant coefficient kills that term.
-/
theorem vanishing {X : Type} {i j : ℕ} (hji : j < i)
    (T : Fin i → NCSeries X) (hT : ∀ k, T k 1 = 0)
    (Q : Fin j → LiePolynomial X) :
    pairing (shuffleList (List.ofFn T)) ((List.ofFn fun k => (Q k).val).prod) = 0 := by
  rw [Lax825748.ShuffleIdentities.pairing_coproduct]
  change ShuffleTensor.tensorPairingLinear T _ = 0
  rw [coproduct_lie_product, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  exact assignment_zero hji T hT Q σ

end Lax825748Proofs.Vanishing
