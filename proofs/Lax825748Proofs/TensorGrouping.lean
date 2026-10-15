import Lax825748Proofs.TensorEvaluation
import Lax825748Proofs.FormalCoordinates

noncomputable section
namespace Lax825748Proofs.TensorGrouping

open Lax825748.Series Lax825748.ShuffleIdentities Lax825748.LieRank
open TensorEvaluation Coproduct ShuffleTensor
open scoped BigOperators

theorem slot_tail_commute {X : Type} {p : ℕ} (P : NCPolynomial X)
    (Q : Fin p → NCPolynomial X) :
    Commute (slotHom (0 : Fin (p + 1)) P) (tailHom p (tensorMonomial Q)) := by
  rw [tensorMonomial, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, tail_slot]
  apply Commute.list_prod_right
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact slot_cross_commute 0 i.succ (Ne.symm (Fin.succ_ne_zero i)) P (Q i)

-- Multiplying a pure tensor by one slot changes only that component.
theorem tensorMonomial_mul_slot {X : Type} {p : ℕ} (Q : Fin p → NCPolynomial X)
    (i : Fin p) (P : NCPolynomial X) :
    tensorMonomial Q * slotHom i P =
      tensorMonomial (Function.update Q i (Q i * P)) := by
  classical
  induction p with
  | zero => exact Fin.elim0 i
  | succ p ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [tensorMonomial_succ, tensorMonomial_succ]
      have ht : (fun j : Fin p => Function.update Q 0 (Q 0 * P) j.succ) =
          (fun j => Q j.succ) := by funext j; simp
      rw [ht, Function.update_self, map_mul]
      have hc := slot_tail_commute P (fun j => Q j.succ)
      rw [mul_assoc, hc.eq.symm, ← mul_assoc]
    · rw [tensorMonomial_succ, tensorMonomial_succ]
      have ht : (fun j : Fin p => Function.update Q i.succ (Q i.succ * P) j.succ) =
          Function.update (fun j => Q j.succ) i (Q i.succ * P) := by
        funext j
        by_cases h : j = i <;> simp [h]
      rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)), ht,
        ← ih, ← tail_slot i P, map_mul, mul_assoc]

def grouped {α X : Type} {p : ℕ} (q : α → NCPolynomial X)
    (l : List (α × Fin p)) (i : Fin p) : NCPolynomial X :=
  ((l.filter fun a => a.2 == i).map fun a => q a.1).prod

theorem assigned_tensor {α X : Type} {p : ℕ} (q : α → NCPolynomial X)
    (l : List (α × Fin p)) :
    (l.map fun a => slotHom a.2 (q a.1)).prod = tensorMonomial (grouped q l) := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp [grouped, tensorMonomial]
  | @append_singleton l a ih =>
    rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ih,
      tensorMonomial_mul_slot]
    congr 1
    funext i
    by_cases hi : i = a.2
    · subst i; simp [grouped]
    · simp [grouped, hi, Ne.symm hi]

theorem assigned_eval {α X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (q : α → NCPolynomial X) (l : List (α × Fin p)) :
    tensorPairingLinear S ((l.map fun a => slotHom a.2 (q a.1)).prod) =
      ∏ i, pairing (S i) (grouped q l i) := by
  rw [assigned_tensor, tensorMonomial_eval]

end Lax825748Proofs.TensorGrouping
