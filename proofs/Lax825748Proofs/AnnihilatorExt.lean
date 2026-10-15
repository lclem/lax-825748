import Lax825748Proofs.CanonicalCoordinates

noncomputable section

namespace Lax825748Proofs.AnnihilatorExt

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator Lax825748.PBW
open Lax825748.Monomials PBWSpanning OrderedSumWords

theorem complementWord_counts {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (l : List (Fin d)) (hl : l.Pairwise (· ≤ ·)) :
    IdealPBW.complementWord P l = orderedPowers (fun i => (P i).val) (fun i => l.count i) := by
  rw [MonomialLists.labels_polynomial]
  have hlist : List.ofFn (MonomialLists.labels fun i => l.count i) = l := by
    rw [MonomialLists.ofFn_labels, MonomialLists.labelsList_counts_eq l hl]
  rw [show (List.ofFn fun k => (P (MonomialLists.labels (fun i => l.count i) k)).val) =
      l.map (fun i => (P i).val) by
        simpa only [List.map_ofFn, Function.comp_def] using
          congrArg (List.map fun i => (P i).val) hlist]
  rfl

theorem annihilator_ext {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (T U : NCSeries X) (hT : InAnnihilator K T) (hU : InAnnihilator K U)
    (hm : ∀ I : Fin d → ℕ, pairing T (orderedPowers (fun i => (P i).val) I) =
      pairing U (orderedPowers (fun i => (P i).val) I)) : T = U := by
  classical
  let κ := Module.Free.ChooseBasisIndex ℝ K
  let : LinearOrder κ := linearOrderOfSTO WellOrderingRel
  let c : Module.Basis κ ℝ K := Module.Free.chooseBasis ℝ K
  have heq : Series.pairingLinear T = Series.pairingLinear U := by
    apply (CanonicalCoordinates.polynomialBasis K P hP c).ext
    intro l
    simp only [CanonicalCoordinates.polynomialBasis_apply, Series.pairingLinear_apply]
    rw [IdealPBW.full_decompose K P hP c l]
    by_cases hv : rightPart l.val = []
    · simp only [hv, evalWord, List.map_nil, List.prod_nil, mul_one]
      rw [complementWord_counts P _ (left_ordered l.val l.property)]
      exact hm _
    · have hj : IdealPBW.complementWord P (leftPart l.val) *
          evalWord (AdaptedBasis.ambientBasis K c) (rightPart l.val) ∈ generatedIdeal K := by
        apply IdealPBW.tailSpan_le_ideal K P c
        exact Submodule.subset_span
          ⟨⟨leftPart l.val, left_ordered l.val l.property⟩,
            ⟨rightPart l.val, right_ordered l.val l.property⟩, hv, rfl⟩
      exact (hT _ hj).trans (hU _ hj).symm
  funext w
  have hh := congrArg (fun f : NCPolynomial X →ₗ[ℝ] ℝ => f (wordPolynomial w)) heq
  simpa only [Series.pairingLinear_apply, Series.pairing_word] using hh

end Lax825748Proofs.AnnihilatorExt
