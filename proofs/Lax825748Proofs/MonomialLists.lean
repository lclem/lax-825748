import Lax825748Proofs.PermutationPairing
import Lax825748.Monomials
import Mathlib.GroupTheory.Perm.DomMulAct

noncomputable section

namespace Lax825748Proofs.MonomialLists

open Lax825748.Series Lax825748.Shuffle Lax825748.ShuffleIdentities Lax825748.Monomials
open scoped BigOperators

theorem shuffleList_append {X : Type} (l m : List (NCSeries X)) :
    shuffleList (l ++ m) = shuffle (shuffleList l) (shuffleList m) := by
  induction l with
  | nil => exact (Shuffle.unit _).symm
  | cons S l ih => simp only [List.cons_append, shuffleList, ih, Shuffle.associative]

theorem shuffleList_flatten {X : Type} (l : List (List (NCSeries X))) :
    shuffleList l.flatten = shuffleList (l.map shuffleList) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatten_cons, shuffleList_append, ih, List.map_cons, shuffleList]

def labelsList {d : ℕ} (I : Fin d → ℕ) : List (Fin d) :=
  (List.ofFn fun i => List.replicate (I i) i).flatten

theorem labelsList_length {d : ℕ} (I : Fin d → ℕ) :
    (labelsList I).length = totalDegree I := by
  simp [labelsList, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, totalDegree]

theorem labelsList_count {d : ℕ} (I : Fin d → ℕ) (i : Fin d) :
    (labelsList I).count i = I i := by
  simp [labelsList, List.count_flatten, List.map_ofFn, Function.comp_def,
    List.count_replicate, List.sum_ofFn]

theorem labelsList_succ {d : ℕ} (I : Fin (d + 1) → ℕ) :
    labelsList I = List.replicate (I 0) 0 ++
      (labelsList fun i => I i.succ).map Fin.succ := by
  simp [labelsList, List.ofFn_succ, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem labelsList_ordered {d : ℕ} (I : Fin d → ℕ) : (labelsList I).Pairwise (· ≤ ·) := by
  induction d with
  | zero => simp [labelsList]
  | succ d ih =>
    rw [labelsList_succ, List.pairwise_append]
    refine ⟨by simp [List.pairwise_replicate], ?_, ?_⟩
    · exact List.Pairwise.map Fin.succ (fun _ _ h => Fin.succ_le_succ_iff.mpr h) (ih _)
    · intro a ha b _
      have ha0 : a = 0 := (List.mem_replicate.mp ha).2
      subst a
      exact Fin.zero_le b

theorem labelsList_counts_eq {d : ℕ} (l : List (Fin d)) (hl : l.Pairwise (· ≤ ·)) :
    labelsList (fun i => l.count i) = l := by
  apply (List.perm_iff_count.mpr ?_).eq_of_pairwise' (labelsList_ordered _) hl
  intro i
  exact labelsList_count _ _

def labels {d : ℕ} (I : Fin d → ℕ) : Fin (totalDegree I) → Fin d :=
  fun k => (labelsList I).get (Fin.cast (labelsList_length I).symm k)

theorem ofFn_cast_get {α : Type} {n : ℕ} (l : List α) (h : l.length = n) :
    (List.ofFn fun i : Fin n => l.get (Fin.cast h.symm i)) = l := by
  subst n
  simp

theorem ofFn_labels {d : ℕ} (I : Fin d → ℕ) : List.ofFn (labels I) = labelsList I :=
  ofFn_cast_get _ (labelsList_length I)

theorem ofFn_cast {α : Type} {n m : ℕ} (h : n = m) (f : Fin m → α) :
    (List.ofFn fun k => f (Fin.cast h k)) = List.ofFn f := by
  subst m
  rfl

theorem count_ofFn {α : Type} [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp [Nat.add_comm]

theorem labels_count {d : ℕ} (I : Fin d → ℕ) (i : Fin d) :
    (List.ofFn (labels I)).count i = I i := by rw [ofFn_labels, labelsList_count]

theorem labels_shuffle {X : Type} {d : ℕ} (S : Fin d → NCSeries X) (I : Fin d → ℕ) :
    shuffleMonomial S I = shuffleList (List.ofFn fun k => S (labels I k)) := by
  have hmap : (labelsList I).map S =
      (List.ofFn fun i => List.replicate (I i) (S i)).flatten := by
    simp [labelsList, List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [show (List.ofFn fun k => S (labels I k)) = (labelsList I).map S by
    rw [← ofFn_labels]; simp [List.map_ofFn, Function.comp_def]]
  rw [hmap, shuffleList_flatten]
  simp [shuffleMonomial, shufflePow, List.map_ofFn, Function.comp_def]

theorem labels_polynomial {X : Type} {d : ℕ} (P : Fin d → NCPolynomial X) (I : Fin d → ℕ) :
    orderedPowers P I = (List.ofFn fun k => P (labels I k)).prod := by
  have hmap : (labelsList I).map P =
      (List.ofFn fun i => List.replicate (I i) (P i)).flatten := by
    simp [labelsList, List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [show (List.ofFn fun k => P (labels I k)) = (labelsList I).map P by
    rw [← ofFn_labels]; simp [List.map_ofFn, Function.comp_def]]
  rw [hmap, List.prod_flatten]
  simp [orderedPowers, List.map_ofFn, Function.comp_def]

end Lax825748Proofs.MonomialLists
