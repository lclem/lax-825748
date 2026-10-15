import Lax825748Proofs.PBWSpanning

noncomputable section

namespace Lax825748Proofs.PositiveSpan

open Lax825748.Series Lax825748.LieRank Lax825748.PBW
open PBWSpanning

def augmentation {X : Type} : NCPolynomial X →ₐ[ℝ] ℝ :=
  MonoidAlgebra.lift ℝ ℝ (Word X) (FreeMonoid.lift (fun _ : X => (0 : ℝ)))

theorem augmentation_lie {X : Type} (P : LiePolynomial X) : augmentation P.val = 0 := by
  apply LieSubalgebra.lieSpan_induction ℝ (x := P.val) (s := Set.range letter)
    (p := fun P _ => augmentation P = 0) ?_ ?_ ?_ ?_ ?_ P.property
  · rintro _ ⟨x, rfl⟩
    simp [augmentation, letter, wordPolynomial]
  · simp
  · intro P Q _ _ hP hQ
    simp only [map_add, hP, hQ, add_zero]
  · intro a P _ hP
    simp only [map_smul, hP, smul_zero]
  · intro P Q _ _ _ _
    simp [LieRing.of_associative_ring_bracket, mul_comm]

def removeConstant {X : Type} : NCPolynomial X →ₗ[ℝ] NCPolynomial X where
  toFun P := P - augmentation P • 1
  map_add' P Q := by simp only [map_add, add_smul]; abel
  map_smul' a P := by simp [smul_sub, smul_smul]

def positiveSpan {X ι : Type} [LinearOrder ι] {L : LieSubalgebra ℝ (NCPolynomial X)}
    (b : Module.Basis ι ℝ L) : Submodule ℝ (NCPolynomial X) :=
  Submodule.span ℝ {P | ∃ l : OrderedWord ι, l.val ≠ [] ∧ P = evalWord b l.val}

theorem augmentation_eval {X ι : Type} {L : LieSubalgebra ℝ (NCPolynomial X)}
    (b : Module.Basis ι ℝ L) (hL : L ≤ liePolynomials X) (l : List ι) (hl : l ≠ []) :
    augmentation (evalWord b l) = 0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons i l =>
    change augmentation ((b i).val * evalWord b l) = 0
    rw [map_mul, augmentation_lie (⟨(b i).val, hL (b i).property⟩ : LiePolynomial X), zero_mul]

theorem removeConstant_ordered_mem {X ι : Type} [LinearOrder ι]
    {L : LieSubalgebra ℝ (NCPolynomial X)} (b : Module.Basis ι ℝ L)
    (hL : L ≤ liePolynomials X) (l : OrderedWord ι) :
    removeConstant (sortedMonomial b l) ∈ positiveSpan b := by
  by_cases hl : l.val = []
  · simp [sortedMonomial, evalWord, hl, removeConstant]
  · change evalWord b l.val - augmentation (evalWord b l.val) • 1 ∈ _
    rw [augmentation_eval b hL l.val hl, zero_smul, sub_zero]
    exact Submodule.subset_span ⟨l, hl, rfl⟩

theorem positive_of_augmentation_zero {X ι : Type} [LinearOrder ι]
    {L : LieSubalgebra ℝ (NCPolynomial X)} (b : Module.Basis ι ℝ L)
    (hL : L ≤ liePolynomials X) (P : NCPolynomial X)
    (hP : P ∈ Submodule.span ℝ (Set.range (sortedMonomial b)))
    (haug : augmentation P = 0) : P ∈ positiveSpan b := by
  have hh : removeConstant P ∈ positiveSpan b := by
    clear haug
    induction hP using Submodule.span_induction with
    | mem P hP => obtain ⟨l, rfl⟩ := hP; exact removeConstant_ordered_mem b hL l
    | zero => simp
    | add P Q _ _ hP hQ => simpa only [map_add] using (positiveSpan b).add_mem hP hQ
    | smul a P _ hP => simpa only [map_smul] using (positiveSpan b).smul_mem a hP
  simpa [removeConstant, haug] using hh

end Lax825748Proofs.PositiveSpan
