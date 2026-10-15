import Lax825748Proofs.TensorGrouping

noncomputable section
namespace Lax825748Proofs.PBWMoments

open Lax825748.Series Lax825748.ShuffleIdentities Lax825748.LieRank
open Lax825748.Annihilator Lax825748.Monomials
open TensorGrouping TensorEvaluation ShuffleTensor MonomialLists
open scoped BigOperators

theorem pbw_word_zero {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hPBW : IsPBWCoordinateFamily P S)
    (i : Fin d) (l : List (Fin d)) (hl : l.Pairwise (· ≤ ·)) (hlen : l.length ≠ 1) :
    pairing (S i) ((l.map fun j => (P j).val).prod) = 0 := by
  classical
  change pairing (S i) (IdealPBW.complementWord P l) = 0
  rw [AnnihilatorExt.complementWord_counts P l hl]
  let I : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => l.count j)
  have hI : (I : Fin d → ℕ) = (fun j => l.count j) :=
    Finsupp.equivFunOnFinite.apply_symm_apply _
  rw [← hI, hPBW]
  apply if_neg
  intro he
  have hh : l = [i] := by
    rw [← labelsList_counts_eq l hl, ← hI, he, CanonicalCoordinates.labelsList_single]
  exact hlen (by simp [hh])

theorem partition_length {α : Type} {p : ℕ} (l : List (α × Fin p)) :
    ∑ i : Fin p, (l.filter fun a => a.2 == i).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.length_cons]
    have he (i : Fin p) :
        (if a.2 == i then a :: l.filter (fun a => a.2 == i)
          else l.filter (fun a => a.2 == i)).length =
        (l.filter fun a => a.2 == i).length + if i = a.2 then 1 else 0 := by
      by_cases h : i = a.2
      · subst i; simp
      · simp [h, Ne.symm h]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih]
    simp

theorem assigned_zero {X : Type} {d p : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hPBW : IsPBWCoordinateFamily P S)
    (T : Fin p → Fin d) (l : List (Fin d × Fin p))
    (hl : (l.map Prod.fst).Pairwise (· ≤ ·)) (hlen : l.length ≠ p) :
    tensorPairingLinear (fun i => S (T i))
      ((l.map fun a => Coproduct.slotHom a.2 (P a.1).val).prod) = 0 := by
  classical
  rw [assigned_eval (fun i => S (T i)) (fun j => (P j).val) l]
  obtain ⟨i, hi⟩ : ∃ i : Fin p, (l.filter fun a => a.2 == i).length ≠ 1 := by
    by_contra! he
    have hh := partition_length l
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hh
    exact hlen hh.symm
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  let r := (l.filter fun a => a.2 == i).map Prod.fst
  have hr : r.Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (List.Sublist.map _ List.filter_sublist) hl
  have hh := pbw_word_zero P S hPBW (T i) r hr
    (by simpa only [r, List.length_map] using hi)
  simpa only [r, List.map_map, Function.comp_def, grouped] using hh

theorem monomial_degree_zero {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hPBW : IsPBWCoordinateFamily P S)
    (I J : Fin d → ℕ) (hdeg : totalDegree I ≠ totalDegree J) :
    pairing (shuffleMonomial S I) (orderedPowers (fun i => (P i).val) J) = 0 := by
  classical
  rw [labels_shuffle, labels_polynomial, Lax825748.ShuffleIdentities.pairing_coproduct]
  change tensorPairingLinear _ _ = 0
  rw [Vanishing.coproduct_lie_product, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  let l := List.ofFn fun k => (labels J k, σ k)
  have hl : (l.map Prod.fst).Pairwise (· ≤ ·) := by
    simpa only [l, List.map_ofFn, Function.comp_def, ofFn_labels] using labelsList_ordered J
  have hh := assigned_zero P S hPBW (labels I) l hl
    (by simpa only [l, List.length_ofFn] using Ne.symm hdeg)
  simpa only [l, List.map_ofFn, Function.comp_def] using hh

theorem monomial_pairing {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (hPBW : IsPBWCoordinateFamily P S) (I J : Fin d →₀ ℕ) :
    pairing (shuffleMonomial S J) (orderedPowers (fun i => (P i).val) I) =
      if J = I then (multiFactorial I : ℝ) else 0 := by
  classical
  by_cases hd : totalDegree J = totalDegree I
  · rw [(Lax825748.ShuffleIdentities.triangular_pairing S P hS hSP J I).2 hd]
    by_cases he : J = I
    · subst J; simp
    · simp [he, show (J : Fin d → ℕ) ≠ I from fun h => he (DFunLike.coe_injective h)]
  · rw [monomial_degree_zero P S hPBW J I hd]
    exact (if_neg (fun h => hd (congrArg (fun K : Fin d →₀ ℕ => totalDegree K) h))).symm

theorem substitution_moment {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (hPBW : IsPBWCoordinateFamily P S) (f : Lax825748.FormalSeries.StateSeries d)
    (I : Fin d →₀ ℕ) :
    pairing (substituteShuffle S f) (orderedPowers (fun i => (P i).val) I) =
      MvPowerSeries.coeff I f * (multiFactorial I : ℝ) := by
  classical
  rw [FormalCoordinates.pairing_substitute P S hS hSP]
  simp only [FormalCoordinates.matrix, monomial_pairing P S hS hSP hPBW]
  rw [Finset.sum_eq_single I]
  · simp
  · intro J _ hJ; rw [if_neg hJ, mul_zero]
  · intro hn; exact (hn (TriangularSystem.mem_indices.mpr (Nat.lt_succ_self _))).elim

/--
---
conclusion: Lax825748.Annihilator.pbw_expansion
---
PBW-dual coordinates give a diagonal moment matrix: a shuffle monomial pairs
only with its matching complementary PBW monomial, with factorial value.
-/
theorem pbw_expansion {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S)
    (hPBW : IsPBWCoordinateFamily P S) (T : NCSeries X) (hT : InAnnihilator K T) :
    ∃ f : Lax825748.FormalSeries.StateSeries d, substituteShuffle S f = T ∧
      ∀ I : Fin d →₀ ℕ, MvPowerSeries.coeff I f =
        pairing T (orderedPowers (fun j => (P j).val) I) / (multiFactorial I : ℝ) := by
  obtain ⟨f, hf, _⟩ := (Lax825748.Annihilator.formal_coordinates K P hP S hS T).mp hT
  refine ⟨f, hf, ?_⟩
  intro I
  have hfac : (multiFactorial I : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (I i))
  apply (eq_div_iff hfac).mpr
  rw [← substitution_moment P S hS.1 hS.2.2 hPBW, hf]

end Lax825748Proofs.PBWMoments
