import Lax825748Proofs.IdealPBW
import Lax825748Proofs.MonomialLists

noncomputable section

namespace Lax825748Proofs.CanonicalCoordinates

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator Lax825748.PBW
open Lax825748.Monomials PBWSpanning OrderedSumWords

def polynomialBasis {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) :
    Module.Basis (OrderedWord (Fin d ⊕ₗ κ)) ℝ (NCPolynomial X) :=
  Module.Basis.mk (Lax825748.PBW.basis (AdaptedBasis.basis K P hP c)).1
    (le_of_eq (Lax825748.PBW.basis (AdaptedBasis.basis K P hP c)).2.symm)

@[simp] theorem polynomialBasis_apply {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (l : OrderedWord (Fin d ⊕ₗ κ)) :
    polynomialBasis K P hP c l = monomial (AdaptedBasis.basis K P hP c) l := by
  simp [polynomialBasis]

def singleIndex {κ : Type} [LinearOrder κ] {d : ℕ} (i : Fin d) : OrderedWord (Fin d ⊕ₗ κ) :=
  ⟨[toLex (Sum.inl i)], by simp⟩

def coefficient {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (i : Fin d) :
    NCPolynomial X →ₗ[ℝ] ℝ :=
  (polynomialBasis K P hP c).coord (singleIndex i)

def coordinates {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (i : Fin d) : NCSeries X :=
  fun w => coefficient K P hP c i (wordPolynomial w)

theorem coefficient_monomial {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K)
    (i : Fin d) (l : OrderedWord (Fin d ⊕ₗ κ)) :
    coefficient K P hP c i (monomial (AdaptedBasis.basis K P hP c) l) =
      if singleIndex i = l then 1 else 0 := by
  change (polynomialBasis K P hP c).coord (singleIndex i)
    (monomial (AdaptedBasis.basis K P hP c) l) = _
  rw [← polynomialBasis_apply K P hP c l]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

theorem coordinate_pairing {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (i : Fin d) (Q : NCPolynomial X) :
    pairing (coordinates K P hP c i) Q = coefficient K P hP c i Q :=
  DualCoordinates.pairing_from_linear _ _

def mixedIndex {κ : Type} [LinearOrder κ] {d : ℕ}
    (u : OrderedWord (Fin d)) (v : OrderedWord κ) : OrderedWord (Fin d ⊕ₗ κ) :=
  ⟨(u.val.map fun i => toLex (Sum.inl i)) ++ (v.val.map fun j => toLex (Sum.inr j)),
    ordered_append u.val v.val u.property v.property⟩

theorem mixed_monomial {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K)
    (u : OrderedWord (Fin d)) (v : OrderedWord κ) :
    IdealPBW.complementWord P u.val * evalWord (AdaptedBasis.ambientBasis K c) v.val =
      monomial (AdaptedBasis.basis K P hP c) (mixedIndex u v) := by
  simp [monomial, mixedIndex, IdealPBW.complementWord, evalWord, List.map_append,
    List.prod_append, List.map_map, Function.comp_def]

theorem single_ne_mixed {κ : Type} [LinearOrder κ] {d : ℕ} (i : Fin d)
    (u : OrderedWord (Fin d)) (v : OrderedWord κ) (hv : v.val ≠ []) :
    singleIndex i ≠ mixedIndex u v := by
  intro he
  have hh := congrArg (fun l : OrderedWord (Fin d ⊕ₗ κ) => rightPart l.val) he
  have hv0 : [] = v.val := by
    change rightPart (([i].map fun a => toLex (Sum.inl a : Fin d ⊕ κ))) =
      rightPart ((u.val.map fun a => toLex (Sum.inl a)) ++
        (v.val.map fun a => toLex (Sum.inr a))) at hh
    simpa only [rightPart_append, rightPart_left, rightPart_right, List.nil_append] using hh
  exact hv hv0.symm

theorem coordinates_annihilate {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (i : Fin d) :
    InAnnihilator K (coordinates K P hP c i) := by
  intro Q hQ
  rw [coordinate_pairing]
  have ht := IdealPBW.ideal_le_tailSpan K P hP c Q hQ
  clear hQ
  induction ht using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨u, v, hv, rfl⟩ := hQ
    rw [mixed_monomial K P hP c u v, coefficient_monomial, if_neg (single_ne_mixed i u v hv)]
  | zero => exact map_zero _
  | add Q R _ _ hQ hR => simp only [map_add, hQ, hR, add_zero]
  | smul a Q _ hQ => simp only [map_smul, hQ, smul_zero]

def pureIndex {κ : Type} [LinearOrder κ] {d : ℕ} (I : Fin d → ℕ) : OrderedWord (Fin d ⊕ₗ κ) :=
  ⟨(MonomialLists.labelsList I).map fun i => toLex (Sum.inl i),
    List.Pairwise.map _ (fun _ _ h => Sum.Lex.inl_le_inl_iff.mpr h)
      (MonomialLists.labelsList_ordered I)⟩

theorem pure_monomial {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (I : Fin d → ℕ) :
    monomial (AdaptedBasis.basis K P hP c) (pureIndex I) =
      orderedPowers (fun j => (P j).val) I := by
  simp only [monomial, pureIndex, List.map_map, Function.comp_def, AdaptedBasis.basis_left]
  rw [MonomialLists.labels_polynomial]
  rw [show (List.ofFn fun k => (P (MonomialLists.labels I k)).val) =
      (MonomialLists.labelsList I).map fun i => (P i).val by
        rw [← MonomialLists.ofFn_labels]
        simp [List.map_ofFn, Function.comp_def]]

theorem labelsList_single {d : ℕ} (i : Fin d) :
    MonomialLists.labelsList (Finsupp.single i 1 : Fin d →₀ ℕ) = [i] := by
  apply (List.perm_iff_count.mpr ?_).eq_of_pairwise'
    (MonomialLists.labelsList_ordered _) (by simp)
  intro j
  simp only [MonomialLists.labelsList_count, Finsupp.single_apply, List.count_cons,
    List.count_nil, zero_add, beq_iff_eq]

theorem single_eq_pure_iff {κ : Type} [LinearOrder κ] {d : ℕ}
    (i : Fin d) (I : Fin d →₀ ℕ) :
    (singleIndex i : OrderedWord (Fin d ⊕ₗ κ)) = pureIndex I ↔ I = Finsupp.single i 1 := by
  constructor
  · intro he
    have hh := congrArg (fun l : OrderedWord (Fin d ⊕ₗ κ) => leftPart l.val) he
    have hl : [i] = MonomialLists.labelsList I := by
      change leftPart (([i].map fun a => toLex (Sum.inl a : Fin d ⊕ κ))) =
        leftPart ((MonomialLists.labelsList I).map fun a => toLex (Sum.inl a)) at hh
      simpa only [leftPart_left] using hh
    ext j
    have hc := congrArg (List.count j) hl.symm
    simpa only [MonomialLists.labelsList_count, Finsupp.single_apply, List.count_cons,
      List.count_nil, zero_add, beq_iff_eq] using hc
  · rintro rfl
    apply Subtype.ext
    simp [singleIndex, pureIndex, labelsList_single]

theorem coordinates_pbw {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) :
    IsPBWCoordinateFamily P (coordinates K P hP c) := by
  intro i I
  rw [coordinate_pairing, ← pure_monomial K P hP c I, coefficient_monomial]
  simp only [single_eq_pure_iff]

theorem coordinates_family {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) :
    IsCoordinateFamily K P (coordinates K P hP c) := by
  refine ⟨?_, coordinates_annihilate K P hP c, ?_⟩
  · intro i
    change coefficient K P hP c i 1 = 0
    have he : (1 : NCPolynomial X) = monomial (AdaptedBasis.basis K P hP c)
        (⟨[], by simp⟩ : OrderedWord (Fin d ⊕ₗ κ)) := rfl
    rw [he, coefficient_monomial]
    simp [singleIndex]
  · intro i j
    rw [coordinate_pairing]
    have he : (P j).val = monomial (AdaptedBasis.basis K P hP c) (singleIndex j) := by
      simp [monomial, singleIndex]
    rw [he, coefficient_monomial]
    simp [singleIndex]

/--
---
conclusion: Lax825748.Annihilator.coordinates_exist
---
Take the coefficients dual to the degree-one complement monomials in an
adapted PBW basis. They vanish on all monomials containing a stabilizer factor.
-/
theorem coordinates_exist {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) :
    ∃ S : Fin d → NCSeries X, IsCoordinateFamily K P S ∧ IsPBWCoordinateFamily P S := by
  classical
  let κ := Module.Free.ChooseBasisIndex ℝ K
  let : LinearOrder κ := linearOrderOfSTO WellOrderingRel
  let c : Module.Basis κ ℝ K := Module.Free.chooseBasis ℝ K
  exact ⟨coordinates K P hP c, coordinates_family K P hP c, coordinates_pbw K P hP c⟩

end Lax825748Proofs.CanonicalCoordinates
