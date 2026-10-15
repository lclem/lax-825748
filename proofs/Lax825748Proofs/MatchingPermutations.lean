import Lax825748Proofs.MonomialLists

noncomputable section

namespace Lax825748Proofs.MatchingPermutations

open MonomialLists
open scoped BigOperators

def matchingSum {d n : ℕ} (f g : Fin n → Fin d) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ k, if f k = g (σ k) then 1 else 0

theorem matching_counts {α : Type} [DecidableEq α] {n : ℕ}
    (f g : Fin n → α) (σ : Equiv.Perm (Fin n))
    (h : ∀ k, f k = g (σ k)) (i : α) :
    (List.ofFn f).count i = (List.ofFn g).count i := by
  rw [count_ofFn, count_ofFn]
  exact Fintype.sum_equiv σ (fun k => if f k = i then 1 else 0)
    (fun k => if g k = i then 1 else 0) (by intro k; rw [h k])

theorem matchingSum_zero {d n : ℕ} (f g : Fin n → Fin d)
    (h : ∃ i, (List.ofFn f).count i ≠ (List.ofFn g).count i) : matchingSum f g = 0 := by
  classical
  obtain ⟨i, hi⟩ := h
  apply Finset.sum_eq_zero
  intro σ _
  have hn : ∃ k, f k ≠ g (σ k) := by
    by_contra! he
    exact hi (matching_counts f g σ he i)
  obtain ⟨k, hk⟩ := hn
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hk]

theorem fiber_card_count {d n : ℕ} (f : Fin n → Fin d) (i : Fin d) :
    Fintype.card {k // f k = i} = (List.ofFn f).count i := by
  simp [Fintype.card_subtype, count_ofFn, Finset.sum_boole]

theorem matchingSum_diagonal {d n : ℕ} (f : Fin n → Fin d) :
    matchingSum f f = ∏ i, (((List.ofFn f).count i).factorial : ℝ) := by
  classical
  have hp (σ : Equiv.Perm (Fin n)) :
      (∏ k, if f k = f (σ k) then (1 : ℝ) else 0) = if f ∘ σ = f then 1 else 0 := by
    by_cases h : f ∘ σ = f
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro k _
      exact if_pos ((congrFun h k).symm)
    · rw [if_neg h]
      have hn : ∃ k, f k ≠ f (σ k) := by
        by_contra! he
        exact h (funext fun k => (he k).symm)
      obtain ⟨k, hk⟩ := hn
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      exact if_neg hk
  simp only [matchingSum, hp, Finset.sum_boole]
  rw [← Fintype.card_subtype (fun σ : Equiv.Perm (Fin n) => f ∘ σ = f),
    DomMulAct.stabilizer_card]
  simp only [Nat.cast_prod, fiber_card_count]

end Lax825748Proofs.MatchingPermutations
