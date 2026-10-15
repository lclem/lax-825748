import Lax825748.PBW
import Lax825748Proofs.TriangularPairing
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section

namespace Lax825748Proofs.DualCoordinates

open Lax825748.Series Lax825748.LieRank

theorem pairing_from_linear {X : Type} (f : NCPolynomial X →ₗ[ℝ] ℝ) (P : NCPolynomial X) :
    pairing (fun w => f (wordPolynomial w)) P = f P := by
  induction P using MonoidAlgebra.induction_on with
  | of w =>
    change pairing (fun w => f (wordPolynomial w)) (wordPolynomial w) = f (wordPolynomial w)
    exact Series.pairing_word _ _
  | add P Q hP hQ => simp only [Series.pairing_add, map_add, hP, hQ]
  | smul a P hP => simp only [Series.pairing_smul, map_smul, hP, smul_eq_mul]

theorem one_not_lie {X : Type} : (1 : NCPolynomial X) ∉ (liePolynomials X).toSubmodule := by
  intro h
  have hp := Lax825748.ShuffleIdentities.lie_primitive 0 (⟨1, h⟩ : LiePolynomial X)
  simp [Coproduct.coproduct_eq_hom] at hp

theorem basis_dual_series {X ι : Type} [DecidableEq ι] (b : Module.Basis ι ℝ (LiePolynomial X)) :
    ∃ S : ι → NCSeries X, (∀ i, S i 1 = 0) ∧
      ∀ i j, pairing (S i) (b j).val = if i = j then 1 else 0 := by
  classical
  have hex (i : ι) : ∃ f : NCPolynomial X →ₗ[ℝ] ℝ,
      f.comp (liePolynomials X).toSubmodule.subtype = b.coord i ∧ f 1 = 0 :=
    LinearMap.exists_extend_of_notMem (b.coord i) one_not_lie 0
  choose f hf hf0 using hex
  refine ⟨fun i w => f i (wordPolynomial w), ?_, ?_⟩
  · intro i
    exact hf0 i
  · intro i j
    rw [pairing_from_linear]
    have hh := congrArg (fun g : LiePolynomial X →ₗ[ℝ] ℝ => g (b j)) (hf i)
    change f i (b j).val = b.coord i (b j) at hh
    simpa [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm] using hh

end Lax825748Proofs.DualCoordinates
