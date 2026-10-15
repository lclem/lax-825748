import Lax825748Proofs.AdaptedBasis
import Lax825748Proofs.PositiveSpan
import Lax825748Proofs.OrderedSumWords

noncomputable section

namespace Lax825748Proofs.IdealPBW

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator Lax825748.PBW
open PBWSpanning OrderedSumWords

def complementWord {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (l : List (Fin d)) : NCPolynomial X := (l.map fun i => (P i).val).prod

def tailSpan {X κ : Type} [LinearOrder κ] {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (c : Module.Basis κ ℝ K) : Submodule ℝ (NCPolynomial X) :=
  Submodule.span ℝ {Q | ∃ u : OrderedWord (Fin d), ∃ v : OrderedWord κ,
    v.val ≠ [] ∧ Q = complementWord P u.val * evalWord (AdaptedBasis.ambientBasis K c) v.val}

theorem full_decompose {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (l : OrderedWord (Fin d ⊕ₗ κ)) :
    monomial (AdaptedBasis.basis K P hP c) l =
      complementWord P (leftPart l.val) *
        evalWord (AdaptedBasis.ambientBasis K c) (rightPart l.val) := by
  change evalWord (AdaptedBasis.basis K P hP c) l.val = _
  calc
    _ = evalWord (AdaptedBasis.basis K P hP c)
        ((leftPart l.val).map (fun i => toLex (Sum.inl i)) ++
          (rightPart l.val).map (fun j => toLex (Sum.inr j))) :=
      congrArg (evalWord _) (split_ordered l.val l.property)
    _ = _ := by
      simp [evalWord, complementWord, List.map_append, List.prod_append, List.map_map,
        Function.comp_def]

theorem prefix_positive_mem {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (c : Module.Basis κ ℝ K) (u : OrderedWord (Fin d))
    (Q : NCPolynomial X) (hQ : Q ∈ PositiveSpan.positiveSpan (AdaptedBasis.ambientBasis K c)) :
    complementWord P u.val * Q ∈ tailSpan K P c := by
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨v, hv, rfl⟩ := hQ
    exact Submodule.subset_span ⟨u, v, hv, rfl⟩
  | zero => simp
  | add Q R _ _ hQ hR => simpa only [mul_add] using (tailSpan K P c).add_mem hQ hR
  | smul a Q _ hQ => simpa only [mul_smul_comm] using (tailSpan K P c).smul_mem a hQ

theorem right_stabilizer_positive {X κ : Type} [LinearOrder κ]
    (K : LieSubalgebraOfPolynomials X) (c : Module.Basis κ ℝ K) (v : List κ) (k : K) :
    evalWord (AdaptedBasis.ambientBasis K c) v * k.val.val ∈
      PositiveSpan.positiveSpan (AdaptedBasis.ambientBasis K c) := by
  let b := AdaptedBasis.ambientBasis K c
  have hh := lie_right_mul b (AdaptedBasis.ambientEquiv K k) (eval_mem b v v.length le_rfl)
  have hs := wordSpan_le_ordered b (v.length + 1) hh
  apply PositiveSpan.positive_of_augmentation_zero b (AdaptedBasis.ambient_le K) _ hs
  rw [map_mul, AdaptedBasis.ambient_member, PositiveSpan.augmentation_lie k.val, mul_zero]

theorem right_stabilizer_mem {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K) (A : NCPolynomial X) (k : K) :
    A * k.val.val ∈ tailSpan K P c := by
  have hA : A ∈ Submodule.span ℝ (Set.range (monomial (AdaptedBasis.basis K P hP c))) := by
    rw [(Lax825748.PBW.basis (AdaptedBasis.basis K P hP c)).2]
    trivial
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨l, rfl⟩ := hA
    rw [full_decompose, mul_assoc]
    exact prefix_positive_mem K P c
      ⟨leftPart l.val, left_ordered l.val l.property⟩ _
      (right_stabilizer_positive K c (rightPart l.val) k)
  | zero => simp
  | add A B _ _ hA hB => simpa only [add_mul] using (tailSpan K P c).add_mem hA hB
  | smul a A _ hA => simpa only [smul_mul_assoc] using (tailSpan K P c).smul_mem a hA

theorem ideal_le_tailSpan {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (c : Module.Basis κ ℝ K)
    (Q : NCPolynomial X) (hQ : Q ∈ generatedIdeal K) : Q ∈ tailSpan K P c := by
  let M : Ideal (NCPolynomial X) :=
    { carrier := {Q | ∀ A, A * Q ∈ tailSpan K P c}
      zero_mem' := by intro A; simp
      add_mem' := by
        intro Q R hQ hR A
        simpa only [mul_add] using (tailSpan K P c).add_mem (hQ A) (hR A)
      smul_mem' := by
        intro A Q hQ B
        change B * (A * Q) ∈ _
        rw [← mul_assoc]
        exact hQ _ }
  have hle : generatedIdeal K ≤ M := by
    apply Ideal.span_le.mpr
    rintro Q ⟨k, rfl⟩ A
    exact right_stabilizer_mem K P hP c A k
  have hh := hle hQ
  simpa using hh 1

theorem tailSpan_le_ideal {X κ : Type} [LinearOrder κ] {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (c : Module.Basis κ ℝ K) : tailSpan K P c ≤ (generatedIdeal K).restrictScalars ℝ := by
  apply Submodule.span_le.mpr
  rintro Q ⟨u, v, hv, rfl⟩
  have he : evalWord (AdaptedBasis.ambientBasis K c) v.val =
      evalWord (AdaptedBasis.ambientBasis K c) v.val.dropLast * (c (v.val.getLast hv)).val.val := by
    conv_lhs => rw [← List.dropLast_append_getLast hv]
    simp [evalWord, List.map_append, List.prod_append]
  change complementWord P u.val * evalWord (AdaptedBasis.ambientBasis K c) v.val ∈ generatedIdeal K
  rw [he, ← mul_assoc]
  apply (generatedIdeal K).mul_mem_left
  exact Ideal.subset_span ⟨c (v.val.getLast hv), rfl⟩

end Lax825748Proofs.IdealPBW
