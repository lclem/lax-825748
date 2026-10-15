import Lax825748.Annihilator
import Lax825748Proofs.PBW
import Mathlib.Data.Sum.Order

noncomputable section

namespace Lax825748Proofs.AdaptedBasis

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator

def combinedFamily {X κ : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (c : Module.Basis κ ℝ K) : κ ⊕ Fin d → LiePolynomial X :=
  Sum.elim (fun j => (c j).val) P

theorem combined_independent {X κ : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) (c : Module.Basis κ ℝ K) :
    LinearIndependent ℝ (combinedFamily K P c) := by
  apply LinearIndependent.sumElim_of_quotient c.linearIndependent P
  exact hP.1

theorem combined_span {X κ : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) (c : Module.Basis κ ℝ K) :
    Submodule.span ℝ (Set.range (combinedFamily K P c)) = ⊤ := by
  have hr : Set.range (fun j => (c j : LiePolynomial X)) =
      K.toSubmodule.subtype '' Set.range c := by
    rw [← Set.range_comp]
    rfl
  rw [combinedFamily, Set.Sum.elim_range, Submodule.span_union, hr, ← Submodule.map_span,
    c.span_eq, Submodule.map_top, Submodule.range_subtype,
    ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  exact hP.2

def basis {X κ : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) (c : Module.Basis κ ℝ K) :
    Module.Basis (Fin d ⊕ₗ κ) ℝ (LiePolynomial X) :=
  (Module.Basis.mk (combined_independent K P hP c) (le_of_eq (combined_span K P hP c).symm)).reindex
    ((Equiv.sumComm κ (Fin d)).trans toLex)

@[simp] theorem basis_left {X κ : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) (c : Module.Basis κ ℝ K)
    (i : Fin d) : basis K P hP c (toLex (Sum.inl i)) = P i := by
  simp [basis, combinedFamily]

@[simp] theorem basis_right {X κ : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) (c : Module.Basis κ ℝ K)
    (j : κ) : basis K P hP c (toLex (Sum.inr j)) = (c j).val := by
  simp [basis, combinedFamily]

def ambient {X : Type} (K : LieSubalgebraOfPolynomials X) : LieSubalgebra ℝ (NCPolynomial X) :=
  K.map (liePolynomials X).incl

def ambientEquiv {X : Type} (K : LieSubalgebraOfPolynomials X) : K ≃ₗ⁅ℝ⁆ ambient K :=
  K.equivMapOfInjective (f := (liePolynomials X).incl) Subtype.val_injective

def ambientBasis {X κ : Type} (K : LieSubalgebraOfPolynomials X)
    (c : Module.Basis κ ℝ K) : Module.Basis κ ℝ (ambient K) :=
  c.map (ambientEquiv K).toLinearEquiv

@[simp] theorem ambient_basis_val {X κ : Type} (K : LieSubalgebraOfPolynomials X)
    (c : Module.Basis κ ℝ K) (j : κ) : (ambientBasis K c j).val = (c j).val.val := rfl

theorem ambient_le {X : Type} (K : LieSubalgebraOfPolynomials X) : ambient K ≤ liePolynomials X := by
  rintro Q ⟨P, _, rfl⟩
  exact P.property

theorem ambient_member {X : Type} (K : LieSubalgebraOfPolynomials X) (k : K) :
    (ambientEquiv K k).val = k.val.val := rfl

end Lax825748Proofs.AdaptedBasis
