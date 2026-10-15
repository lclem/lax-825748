import Lax825748Proofs.PBWMoments

noncomputable section
namespace Lax825748Proofs.MomentComparison

open Lax825748.Series Lax825748.Shuffle Lax825748.ShuffleIdentities Lax825748.LieRank
open Lax825748.Annihilator Lax825748.Monomials
open TensorGrouping TensorEvaluation ShuffleTensor MonomialLists
open scoped BigOperators

theorem family_moments {X : Type} {d p : ℕ} (P : Fin d → LiePolynomial X)
    (S T : Fin p → NCSeries X)
    (hST : ∀ i (I : Fin d → ℕ),
      pairing (S i) (orderedPowers (fun j => (P j).val) I) =
      pairing (T i) (orderedPowers (fun j => (P j).val) I)) (I : Fin d → ℕ) :
    pairing (shuffleList (List.ofFn S)) (orderedPowers (fun j => (P j).val) I) =
    pairing (shuffleList (List.ofFn T)) (orderedPowers (fun j => (P j).val) I) := by
  classical
  rw [labels_polynomial, Lax825748.ShuffleIdentities.pairing_coproduct,
    Lax825748.ShuffleIdentities.pairing_coproduct]
  change tensorPairingLinear S _ = tensorPairingLinear T _
  rw [Vanishing.coproduct_lie_product, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  let l := List.ofFn fun k => (labels I k, σ k)
  have he (U : Fin p → NCSeries X) :
      tensorPairingLinear U ((List.ofFn fun k => Coproduct.slotHom (σ k) (P (labels I k)).val).prod) =
      ∏ i, pairing (U i) (grouped (fun j => (P j).val) l i) := by
    simpa only [l, List.map_ofFn, Function.comp_def] using
      assigned_eval U (fun j => (P j).val) l
  rw [he S, he T]
  apply Finset.prod_congr rfl
  intro i _
  let r := (l.filter fun a => a.2 == i).map Prod.fst
  have hl : (l.map Prod.fst).Pairwise (· ≤ ·) := by
    simpa only [l, List.map_ofFn, Function.comp_def, ofFn_labels] using labelsList_ordered I
  have hr : r.Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) hl
  have hh := hST i (fun j => r.count j)
  rw [← AnnihilatorExt.complementWord_counts P r hr] at hh
  simpa only [r, IdealPBW.complementWord, List.map_map, Function.comp_def, grouped] using hh

theorem shuffle_moments {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S T U V : NCSeries X)
    (hSU : ∀ I : Fin d → ℕ, pairing S (orderedPowers (fun j => (P j).val) I) =
      pairing U (orderedPowers (fun j => (P j).val) I))
    (hTV : ∀ I : Fin d → ℕ, pairing T (orderedPowers (fun j => (P j).val) I) =
      pairing V (orderedPowers (fun j => (P j).val) I)) (I : Fin d → ℕ) :
    pairing (shuffle S T) (orderedPowers (fun j => (P j).val) I) =
    pairing (shuffle U V) (orderedPowers (fun j => (P j).val) I) := by
  have hh := family_moments P ![S,T] ![U,V] (by
    intro i J; fin_cases i
    · exact hSU J
    · exact hTV J) I
  simpa [List.ofFn_succ, shuffleList, Shuffle.commutative T (constantSeries 1),
    Shuffle.commutative V (constantSeries 1), Shuffle.unit] using hh

end Lax825748Proofs.MomentComparison
