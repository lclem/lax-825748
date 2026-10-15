import Lax825748Proofs.MatchingPermutations

noncomputable section

namespace Lax825748Proofs.TriangularPairing

open Lax825748.Series Lax825748.LieRank Lax825748.Monomials Lax825748.ShuffleIdentities
open MonomialLists MatchingPermutations

/--
---
conclusion: Lax825748.ShuffleIdentities.triangular_pairing
---
Expand each multi-index into its list of repeated labels. Below the diagonal
use vanishing; on the diagonal the surviving permutations preserve labels,
so their number is the product of the factorials of the multiplicities.
-/
theorem triangular_pairing {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (P : Fin d → LiePolynomial X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (I J : Fin d → ℕ) :
    (totalDegree J < totalDegree I →
      pairing (shuffleMonomial S I) (orderedPowers (fun i => (P i).val) J) = 0) ∧
    (totalDegree I = totalDegree J →
      pairing (shuffleMonomial S I) (orderedPowers (fun i => (P i).val) J) =
        if I = J then (multiFactorial I : ℝ) else 0) := by
  classical
  constructor
  · intro hJI
    rw [labels_shuffle, labels_polynomial]
    exact Lax825748.ShuffleIdentities.vanishing hJI _ (fun k => hS _) (fun k => P (labels J k))
  · intro hdeg
    by_cases hIJ : I = J
    · subst J
      rw [if_pos rfl, labels_shuffle, labels_polynomial,
        Lax825748.ShuffleIdentities.permutation_pairing _ (fun k => hS _) (fun k => P (labels I k))]
      simp_rw [hSP]
      change matchingSum (labels I) (labels I) = _
      rw [matchingSum_diagonal]
      simp only [labels_count, multiFactorial, Nat.cast_prod]
    · rw [if_neg hIJ]
      have hpoly : orderedPowers (fun i => (P i).val) J =
          (List.ofFn fun k : Fin (totalDegree I) => (P (labels J (Fin.cast hdeg k))).val).prod := by
        rw [labels_polynomial]
        exact congrArg List.prod (ofFn_cast hdeg (fun k => (P (labels J k)).val)).symm
      rw [labels_shuffle, hpoly,
        Lax825748.ShuffleIdentities.permutation_pairing _ (fun k => hS _)
          (fun k => P (labels J (Fin.cast hdeg k)))]
      simp_rw [hSP]
      change matchingSum (labels I) (fun k => labels J (Fin.cast hdeg k)) = 0
      apply matchingSum_zero
      obtain ⟨i, hi⟩ : ∃ i, I i ≠ J i := by
        by_contra! he
        exact hIJ (funext he)
      refine ⟨i, ?_⟩
      rw [labels_count, ofFn_cast hdeg, labels_count]
      exact hi

end Lax825748Proofs.TriangularPairing
