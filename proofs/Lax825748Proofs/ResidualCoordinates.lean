import Lax825748Proofs.ResidualKernel
import Lax825748Proofs.Projection
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
namespace Lax825748Proofs.ResidualCoordinates

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator

-- Restrict the coefficient pairing to the finite-dimensional residual space.
def residualPairing {X : Type} (f : NCSeries X) :
    residualSpace f →ₗ[ℝ] NCPolynomial X →ₗ[ℝ] ℝ where
  toFun T := Series.pairingLinear T.val
  map_add' T U := by
    apply LinearMap.ext
    intro Q
    exact Series.pairing_add_series T.val U.val Q
  map_smul' a T := by
    apply LinearMap.ext
    intro Q
    exact Series.pairing_smul_series a T.val Q

theorem residualPairing_injective {X : Type} (f : NCSeries X) :
    Function.Injective (residualPairing f) := by
  intro T U h
  apply Subtype.ext
  funext w
  have hh := congrArg (fun φ : NCPolynomial X →ₗ[ℝ] ℝ => φ (wordPolynomial w)) h
  simpa only [residualPairing, LinearMap.coe_mk, AddHom.coe_mk,
    Series.pairingLinear_apply, Series.pairing_word] using hh

theorem kernel_eq {X : Type} (f : NCSeries X) (K : LieSubalgebraOfPolynomials X)
    (hK : ∀ L : LiePolynomial X, L ∈ K ↔ leftResidual L.val f = 0) :
    K = ResidualKernel.kernel f := by
  ext L
  exact hK L

theorem dual_polynomials {X : Type} {k : ℕ} (f : NCSeries X)
    (K : LieSubalgebraOfPolynomials X)
    (hK : ∀ L : LiePolynomial X, L ∈ K ↔ leftResidual L.val f = 0)
    (P : Fin k → LiePolynomial X) (hP : IsComplement K P) :
    ∃ Q : Fin k → NCPolynomial X, ∀ i j, pairing f (Q i * (P j).val) = if i = j then 1 else 0 := by
  classical
  rw [kernel_eq f K hK] at hP
  let bq : Module.Basis (Fin k) ℝ (LiePolynomial X ⧸ (ResidualKernel.kernel f).toSubmodule) :=
    Module.Basis.mk hP.1 (le_of_eq hP.2.symm)
  let b : Module.Basis (Fin k) ℝ (residualSpace f) := bq.map (ResidualKernel.quotientEquiv f)
  let : Module.Finite ℝ (residualSpace f) := Module.Finite.of_basis b
  have hs : Function.Surjective (residualPairing f).flip :=
    LinearMap.flip_surjective_iff₁.mpr (residualPairing_injective f)
  choose Q hQ using fun i : Fin k => hs (b.coord i)
  refine ⟨Q, ?_⟩
  intro i j
  have hh := congrArg (fun φ : residualSpace f →ₗ[ℝ] ℝ => φ (b j)) (hQ i)
  change pairing (b j).val (Q i) = b.coord i (b j) at hh
  have hb : (b j).val = leftResidual (P j).val f := by
    simp only [b, Module.Basis.map_apply, bq, Module.Basis.mk_apply]
    rfl
  rw [hb, Series.pairing_left_residual] at hh
  simpa only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using hh

theorem pairing_sub_series {X : Type} (T U : NCSeries X) (Q : NCPolynomial X) :
    pairing (T - U) Q = pairing T Q - pairing U Q := by
  have he : T - U = T + (-1 : ℝ) • U := by simp [sub_eq_add_neg]
  rw [he, Series.pairing_add_series, Series.pairing_smul_series]
  ring

theorem constant_pairing_lie {X : Type} (a : ℝ) (P : LiePolynomial X) :
    pairing (constantSeries a) P.val = 0 := by
  apply Projection.constant_ann (⊤ : LieSubalgebraOfPolynomials X) a
  exact Ideal.subset_span ⟨⟨P, by trivial⟩, rfl⟩

def coordinates {X : Type} {k : ℕ} (f : NCSeries X) (Q : Fin k → NCPolynomial X)
    (i : Fin k) : NCSeries X := rightResidual f (Q i) - constantSeries (pairing f (Q i))

theorem coordinates_family {X : Type} {k : ℕ} (f : NCSeries X)
    (K : LieSubalgebraOfPolynomials X)
    (hK : ∀ L : LiePolynomial X, L ∈ K ↔ leftResidual L.val f = 0)
    (P : Fin k → LiePolynomial X) (Q : Fin k → NCPolynomial X)
    (hQ : ∀ i j, pairing f (Q i * (P j).val) = if i = j then 1 else 0) :
    IsCoordinateFamily K P (coordinates f Q) := by
  have hf : InAnnihilator K f := by
    rw [kernel_eq f K hK]
    exact ResidualKernel.series_ann f
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [coordinates, Pi.sub_apply, rightResidual, constantSeries]
    change pairing f (Q i * 1) - pairing f (Q i) = 0
    rw [mul_one, sub_self]
  · intro i T hT
    rw [coordinates, pairing_sub_series,
      Lax825748.Annihilator.closed_residual K f hf (Q i) T hT,
      Projection.constant_ann K _ T hT, sub_self]
  · intro i j
    rw [coordinates, pairing_sub_series, Series.pairing_right_residual,
      constant_pairing_lie, sub_zero]
    exact hQ i j

end Lax825748Proofs.ResidualCoordinates
