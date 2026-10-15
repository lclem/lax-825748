import Lax825748Proofs.Rank
import Lax825748Proofs.FormalCoordinates

noncomputable section
namespace Lax825748Proofs.ResidualKernel

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator

def residualMap {X : Type} (g : NCSeries X) : LiePolynomial X →ₗ[ℝ] NCSeries X where
  toFun P := leftResidual P.val g
  map_add' P Q := by funext w; simp [leftResidual, mul_add]
  map_smul' a P := by funext w; simp [leftResidual]

theorem residual_pairing {X : Type} (g : NCSeries X) (P : LiePolynomial X)
    (A : NCPolynomial X) :
    pairing g (A * P.val) = pairing (residualMap g P) A :=
  (Series.pairing_left_residual g P.val A).symm

theorem kernel_lie {X : Type} (g : NCSeries X) (P Q : LiePolynomial X)
    (hP : residualMap g P = 0) (hQ : residualMap g Q = 0) :
    residualMap g ⁅P,Q⁆ = 0 := by
  funext w
  change pairing g (wordPolynomial w * (P.val * Q.val - Q.val * P.val)) = 0
  rw [mul_sub, ← mul_assoc, ← mul_assoc]
  change Series.pairingLinear g (_ - _) = 0
  rw [map_sub, Series.pairingLinear_apply, Series.pairingLinear_apply,
    residual_pairing g Q, residual_pairing g P, hP, hQ]
  simp [pairing]

def kernel {X : Type} (g : NCSeries X) : LieSubalgebraOfPolynomials X where
  __ := LinearMap.ker (residualMap g)
  lie_mem' hP hQ := kernel_lie g _ _ hP hQ

theorem series_ann {X : Type} (g : NCSeries X) : InAnnihilator (kernel g) g := by
  intro P hP
  have hall : ∀ Q ∈ generatedIdeal (kernel g), ∀ A : NCPolynomial X,
      pairing g (A * Q) = 0 := by
    intro Q hQ
    change Q ∈ Submodule.span (NCPolynomial X) {P | ∃ k : kernel g, P = k.val.val} at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨k, rfl⟩ := hQ
      intro A
      rw [residual_pairing, k.property]
      simp [pairing]
    | zero => intro A; simp
    | add Q R _ _ hQ hR => intro A; simp [mul_add, hQ, hR]
    | smul B Q _ hQ => intro A; exact (by
        change pairing g (A * (B * Q)) = 0
        rw [← mul_assoc]
        exact hQ (A * B))
  simpa only [one_mul] using hall P hP 1

theorem range_eq {X : Type} (g : NCSeries X) :
    LinearMap.range (residualMap g) = residualSpace g := by
  apply le_antisymm
  · rintro T ⟨P, rfl⟩
    exact Submodule.subset_span ⟨P, rfl⟩
  · apply Submodule.span_le.mpr
    rintro T ⟨P, rfl⟩
    exact ⟨P, rfl⟩

def quotientEquiv {X : Type} (g : NCSeries X) :
    (LiePolynomial X ⧸ (kernel g).toSubmodule) ≃ₗ[ℝ] residualSpace g :=
  (residualMap g).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ (range_eq g))

theorem complement_exists {X : Type} (g : NCSeries X) (d : ℕ) (hr : HasLieRank g d) :
    ∃ P : Fin d → LiePolynomial X, IsComplement (kernel g) P := by
  let := hr.1
  let e := quotientEquiv g
  let b : Module.Basis (Fin d) ℝ (residualSpace g) :=
    (Module.finBasis ℝ (residualSpace g)).reindex (finCongr hr.2)
  let c := b.map e.symm
  choose P hP using fun i : Fin d => (kernel g).toSubmodule.mkQ_surjective (c i)
  refine ⟨P, ?_, ?_⟩
  · simpa only [hP] using c.linearIndependent
  · simpa only [hP] using c.span_eq

end Lax825748Proofs.ResidualKernel
