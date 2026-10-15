import Lax825748.CDA
import Lax825748Proofs.ContinuousDerivations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPowerSeries.Rename

noncomputable section
namespace Lax825748Proofs.CDAAlgebra

open Lax825748.FormalSeries Lax825748.CDA
open scoped BigOperators Matrix

theorem killCompl_pderiv {d k : ℕ} (e : Fin k ↪ Fin d)
    (i : Fin k) (f : StateSeries d) :
    MvPowerSeries.killCompl e (MvPowerSeries.pderiv ℝ (e i) f) =
      MvPowerSeries.pderiv ℝ i (MvPowerSeries.killCompl e f) := by
  ext n
  simp only [MvPowerSeries.coeff_killCompl, MvPowerSeries.coeff_pderiv]
  simp [Finsupp.embDomain_add, Finsupp.embDomain_single]

theorem restrict_algebra {d k : ℕ} (e : Fin k ↪ Fin d)
    (C : Subalgebra ℝ (StateSeries d)) (hfg : C.FG) (hs : DerivativeStable C) :
    (C.map (MvPowerSeries.killCompl e)).FG ∧
      DerivativeStable (C.map (MvPowerSeries.killCompl e)) := by
  refine ⟨hfg.map _, ?_⟩
  intro i f hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact ⟨MvPowerSeries.pderiv ℝ (e i) g, hs (e i) g hg, killCompl_pderiv e i g⟩

def fieldDerivation {d : ℕ} (V : VectorField d) :
    Derivation ℝ (StateSeries d) (StateSeries d) where
  toFun := applyVectorField V
  map_add' := RepresentationMap.field_add V
  map_smul' := RepresentationMap.field_smul V
  map_one_eq_zero' := RepresentationMap.field_C V 1
  leibniz' f g := by
    change applyVectorField V (f * g) = f * applyVectorField V g + g * applyVectorField V f
    rw [RepresentationMap.field_mul]
    ring

theorem det_mem {d : ℕ} (B : Subalgebra ℝ (StateSeries d))
    (M : Matrix (Fin d) (Fin d) (StateSeries d)) (hM : ∀ i j, M i j ∈ B) :
    M.det ∈ B := by
  let N : Matrix (Fin d) (Fin d) B := fun i j => ⟨M i j, hM i j⟩
  have h := B.val.map_det N
  change (↑(N.det) : StateSeries d) = M.det at h
  exact h ▸ (N.det).property

theorem adjugate_mem {d : ℕ} (B : Subalgebra ℝ (StateSeries d))
    (M : Matrix (Fin d) (Fin d) (StateSeries d)) (hM : ∀ i j, M i j ∈ B)
    (i j : Fin d) : M.adjugate i j ∈ B := by
  let N : Matrix (Fin d) (Fin d) B := fun i j => ⟨M i j, hM i j⟩
  have h := congrArg (fun A => A i j) (B.val.map_adjugate N)
  change (↑(N.adjugate i j) : StateSeries d) = M.adjugate i j at h
  exact h ▸ (N.adjugate i j).property

theorem inverse_extension_stable {d : ℕ} (B : Subalgebra ℝ (StateSeries d))
    (D : Derivation ℝ (StateSeries d) (StateSeries d))
    (hB : ∀ f ∈ B, D f ∈ B) (b : StateSeries d) (hb : b ∈ B)
    (hu : MvPowerSeries.constantCoeff b ≠ 0) :
    ∀ f ∈ B ⊔ Algebra.adjoin ℝ ({b⁻¹} : Set (StateSeries d)),
      D f ∈ B ⊔ Algebra.adjoin ℝ ({b⁻¹} : Set (StateSeries d)) := by
  let C := B ⊔ Algebra.adjoin ℝ ({b⁻¹} : Set (StateSeries d))
  have hBC : B ≤ C := le_sup_left
  have hinv : b⁻¹ ∈ C := (show Algebra.adjoin ℝ {b⁻¹} ≤ C from le_sup_right)
    (Algebra.subset_adjoin (Set.mem_singleton b⁻¹))
  let E : Subalgebra ℝ (StateSeries d) :=
    { carrier := {f | f ∈ C ∧ D f ∈ C}
      algebraMap_mem' := by intro r; exact ⟨C.algebraMap_mem r, by simp⟩
      zero_mem' := ⟨C.zero_mem, by simp⟩
      one_mem' := ⟨C.one_mem, by simp⟩
      add_mem' := by
        rintro f g ⟨hf, hDf⟩ ⟨hg, hDg⟩
        exact ⟨C.add_mem hf hg, by simpa using C.add_mem hDf hDg⟩
      mul_mem' := by
        rintro f g ⟨hf, hDf⟩ ⟨hg, hDg⟩
        exact ⟨C.mul_mem hf hg, by
          simpa only [D.leibniz, smul_eq_mul] using
            C.add_mem (C.mul_mem hf hDg) (C.mul_mem hg hDf)⟩ }
  have hCE : C ≤ E := by
    refine sup_le (fun f hf => ⟨hBC hf, hBC (hB f hf)⟩) ?_
    apply Algebra.adjoin_le
    rintro f (rfl : f = b⁻¹)
    refine ⟨hinv, ?_⟩
    rw [D.leibniz_of_mul_eq_one (MvPowerSeries.inv_mul_cancel b hu), smul_eq_mul]
    exact C.mul_mem (C.neg_mem (C.pow_mem hinv 2)) (hBC (hB b hb))
  intro f hf
  exact (hCE hf).2

theorem localize_frame {d : ℕ} (B : Subalgebra ℝ (StateSeries d))
    (hfg : B.FG) (hX : ∀ i : Fin d, MvPowerSeries.X i ∈ B)
    (V : Fin d → VectorField d)
    (hstable : ∀ j f, f ∈ B → applyVectorField (V j) f ∈ B)
    (hzero : ∀ i j, MvPowerSeries.constantCoeff (V i j) = if i = j then 1 else 0) :
    ∃ C : Subalgebra ℝ (StateSeries d), C.FG ∧ DerivativeStable C ∧ B ≤ C := by
  classical
  let M : Matrix (Fin d) (Fin d) (StateSeries d) := V
  have hM : ∀ i j, M i j ∈ B := by
    intro i j
    simpa only [ContinuousDerivations.field_X] using hstable i _ (hX j)
  have hdet : M.det ∈ B := det_mem B M hM
  have hunit : MvPowerSeries.constantCoeff M.det ≠ 0 := by
    rw [RingHom.map_det]
    have hid : MvPowerSeries.constantCoeff.mapMatrix M = 1 := by
      ext i j
      exact hzero i j
    rw [hid, Matrix.det_one]
    exact one_ne_zero
  let C := B ⊔ Algebra.adjoin ℝ ({M.det⁻¹} : Set (StateSeries d))
  have hBC : B ≤ C := le_sup_left
  have hinv : M.det⁻¹ ∈ C :=
    (show Algebra.adjoin ℝ {M.det⁻¹} ≤ C from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_singleton _))
  have hfginv : (Algebra.adjoin ℝ ({M.det⁻¹} : Set (StateSeries d))).FG := by
    simpa using (Subalgebra.fg_adjoin_finset (R := ℝ) {M.det⁻¹})
  refine ⟨C, hfg.sup hfginv, ?_, hBC⟩
  intro i f hf
  have hV : ∀ j, applyVectorField (V j) f ∈ C := fun j =>
    inverse_extension_stable B (fieldDerivation (V j)) (hstable j) M.det hdet hunit f hf
  let df : Fin d → StateSeries d := fun j => MvPowerSeries.pderiv ℝ j f
  have hid : M.adjugate *ᵥ (M *ᵥ df) = M.det • df := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congrFun hid i
  change (∑ j, M.adjugate i j * applyVectorField (V j) f) =
    M.det * MvPowerSeries.pderiv ℝ i f at hi
  have hsum : (∑ j, M.adjugate i j * applyVectorField (V j) f) ∈ C := by
    apply C.sum_mem
    intro j _
    exact C.mul_mem (hBC (adjugate_mem B M hM i j)) (hV j)
  have hm := C.mul_mem hinv hsum
  rw [hi, ← mul_assoc, MvPowerSeries.inv_mul_cancel M.det hunit, one_mul] at hm
  exact hm

end Lax825748Proofs.CDAAlgebra
