import Lax825748Proofs.DualCoordinates
import Mathlib.Data.List.Sort

noncomputable section

namespace Lax825748Proofs.PBWIndependence

open Lax825748.Series Lax825748.Shuffle Lax825748.LieRank Lax825748.PBW
open scoped BigOperators

def dualWord {X ι : Type} (S : ι → NCSeries X) (l : List ι) : NCSeries X :=
  shuffleList (l.map S)

theorem ofFn_get_map {α β : Type} (l : List α) (f : α → β) :
    (List.ofFn fun k => f (l.get k)) = l.map f := by
  simp

theorem word_pairing_lower {X ι : Type} (b : Module.Basis ι ℝ (LiePolynomial X))
    (S : ι → NCSeries X) (hS : ∀ i, S i 1 = 0) (l m : List ι) (hl : m.length < l.length) :
    pairing (dualWord S l) ((m.map fun i => (b i).val).prod) = 0 := by
  rw [dualWord, ← ofFn_get_map l S, ← ofFn_get_map m (fun i => (b i).val)]
  exact Lax825748.ShuffleIdentities.vanishing hl _ (fun k => hS _) (fun k => b (m.get k))

theorem word_pairing_equal {X ι : Type} [DecidableEq ι]
    (b : Module.Basis ι ℝ (LiePolynomial X)) (S : ι → NCSeries X)
    (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (b j).val = if i = j then 1 else 0)
    (l m : List ι) (hlen : l.length = m.length) :
    pairing (dualWord S l) ((m.map fun i => (b i).val).prod) =
      ∑ σ : Equiv.Perm (Fin l.length), ∏ k,
        if l.get k = m.get (Fin.cast hlen (σ k)) then (1 : ℝ) else 0 := by
  have hm : (List.ofFn fun k : Fin l.length => (b (m.get (Fin.cast hlen k))).val) =
      m.map (fun i => (b i).val) := by
    rw [MonomialLists.ofFn_cast hlen (fun k => (b (m.get k)).val)]
    exact ofFn_get_map m (fun i => (b i).val)
  rw [dualWord, ← ofFn_get_map l S, ← hm]
  rw [Lax825748.ShuffleIdentities.permutation_pairing _ (fun k => hS _)
    (fun k => b (m.get (Fin.cast hlen k)))]
  simp only [hSP]

theorem word_pairing_off_diagonal {X ι : Type} [LinearOrder ι]
    (b : Module.Basis ι ℝ (LiePolynomial X)) (S : ι → NCSeries X)
    (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (b j).val = if i = j then 1 else 0)
    (l m : OrderedWord ι) (hlen : l.val.length = m.val.length) (hne : l ≠ m) :
    pairing (dualWord S l.val) (monomial b m) = 0 := by
  rw [monomial, word_pairing_equal b S hS hSP l.val m.val hlen]
  apply Finset.sum_eq_zero
  intro σ _
  have hn : ∃ k, l.val.get k ≠ m.val.get (Fin.cast hlen (σ k)) := by
    by_contra! he
    have hperm : l.val.Perm m.val := by
      apply List.perm_iff_count.mpr
      intro i
      have hc := MatchingPermutations.matching_counts l.val.get
        (fun k => m.val.get (Fin.cast hlen k)) σ he i
      simpa only [List.ofFn_get, MonomialLists.ofFn_cast_get m.val hlen.symm] using hc
    exact hne (Subtype.ext (hperm.eq_of_pairwise' l.property m.property))
  obtain ⟨k, hk⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

theorem word_pairing_diagonal_pos {X ι : Type} [DecidableEq ι]
    (b : Module.Basis ι ℝ (LiePolynomial X)) (S : ι → NCSeries X)
    (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (b j).val = if i = j then 1 else 0)
    (l : List ι) : 0 < pairing (dualWord S l) ((l.map fun i => (b i).val).prod) := by
  rw [word_pairing_equal b S hS hSP l l rfl]
  apply Finset.sum_pos'
  · intro σ _
    apply Finset.prod_nonneg
    intro k _
    split_ifs <;> norm_num
  · refine ⟨Equiv.refl _, Finset.mem_univ _, ?_⟩
    simp

theorem linearIndependent {X ι : Type} [LinearOrder ι]
    (b : Module.Basis ι ℝ (LiePolynomial X)) : LinearIndependent ℝ (monomial b) := by
  classical
  obtain ⟨S, hS, hSP⟩ := DualCoordinates.basis_dual_series b
  apply linearIndependent_iff.mpr
  intro a ha
  by_contra hne
  have hs : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  obtain ⟨l, hl, hmax⟩ := a.support.exists_max_image (fun l : OrderedWord ι => l.val.length) hs
  have he := congrArg (Series.pairingLinear (dualWord S l.val)) ha
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul,
    Series.pairingLinear_apply, Series.pairing_zero, smul_eq_mul] at he
  change (∑ m ∈ a.support, a m * pairing (dualWord S l.val) (monomial b m)) = 0 at he
  rw [Finset.sum_eq_single l] at he
  · exact mul_ne_zero (Finsupp.mem_support_iff.mp hl)
      (ne_of_gt (word_pairing_diagonal_pos b S hS hSP l.val)) he
  · intro m hm hml
    have hmle := hmax m hm
    have hz : pairing (dualWord S l.val) (monomial b m) = 0 := by
      rcases lt_or_eq_of_le hmle with hlt | heq
      · exact word_pairing_lower b S hS l.val m.val hlt
      · exact word_pairing_off_diagonal b S hS hSP l m heq.symm (Ne.symm hml)
    rw [hz, mul_zero]
  · exact fun hnot => False.elim (hnot hl)

end Lax825748Proofs.PBWIndependence
