import Lax825748Proofs.TensorEvaluation

noncomputable section

namespace Lax825748Proofs.PermutationPairing

open Lax825748.Series Lax825748.LieRank Lax825748.Shuffle Lax825748.ShuffleIdentities
open scoped BigOperators

theorem sum_assignments {n : ℕ} (F : (Fin n → Fin n) → ℝ)
    (hF : ∀ f, ¬ Function.Surjective f → F f = 0) :
    (∑ f : Fin n → Fin n, F f) = ∑ σ : Equiv.Perm (Fin n), F σ := by
  classical
  let B := Finset.univ.filter (fun f : Fin n → Fin n => Function.Bijective f)
  calc
    _ = ∑ f ∈ B, F f := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      apply hF f
      intro hs
      apply hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, Finite.surjective_iff_bijective.mp hs⟩
    _ = _ := by
      symm
      apply Finset.sum_bij (fun (σ : Equiv.Perm (Fin n)) _ => (σ : Fin n → Fin n))
      · intro σ _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
      · intro σ _ τ _ h
        exact Equiv.ext (congrFun h)
      · intro f hf
        exact ⟨Equiv.ofBijective f (Finset.mem_filter.mp hf).2, Finset.mem_univ _, rfl⟩
      · intro σ _
        rfl

/--
---
conclusion: Lax825748.ShuffleIdentities.permutation_pairing
---
Expand the coproduct over assignments of Lie factors to tensor slots.
Nonsurjective assignments vanish, and the bijective ones are permutations.
-/
theorem permutation_pairing {X : Type} {n : ℕ}
    (T : Fin n → NCSeries X) (hT : ∀ k, T k 1 = 0)
    (Q : Fin n → LiePolynomial X) :
    pairing (shuffleList (List.ofFn T)) ((List.ofFn fun k => (Q k).val).prod) =
      ∑ σ : Equiv.Perm (Fin n), ∏ k, pairing (T k) (Q (σ k)).val := by
  classical
  rw [Lax825748.ShuffleIdentities.pairing_coproduct]
  change ShuffleTensor.tensorPairingLinear T _ = _
  rw [Vanishing.coproduct_lie_product, map_sum]
  rw [sum_assignments _ (fun f hf => Vanishing.assignment_zero_of_not_surjective T hT Q f hf)]
  simp only [TensorEvaluation.permutation_tensor_eval]
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
    { toFun := Equiv.symm
      invFun := Equiv.symm
      left_inv := fun σ => by simp
      right_inv := fun σ => by simp }
  apply Fintype.sum_equiv e
  intro σ
  exact Fintype.prod_equiv σ (fun i => pairing (T (σ i)) (Q i).val)
    (fun i => pairing (T i) (Q (σ.symm i)).val) (by intro i; simp)

end Lax825748Proofs.PermutationPairing
