import Lax825748.ResidualConvergence
import Lax825748Proofs.NecessaryConvergence
import Lax825748Proofs.Series

noncomputable section

namespace Lax825748Proofs.ResidualConvergence

open Lax825748.Series Lax825748.LieRank Lax825748.Monomials
open Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.ConvergenceHypothesis
open Lax825748Proofs

theorem holds_add {X : Type} {g h : NCSeries X} (hg : Holds g) (hh : Holds h) :
    Holds (g + h) := by
  intro q P
  obtain ⟨α, hα, C, hC, hb⟩ := hg q P
  obtain ⟨β, hβ, D, hD, hd⟩ := hh q P
  refine ⟨α + β, add_pos hα hβ, max C D, lt_max_iff.mpr (.inl hC), ?_⟩
  intro I
  rw [Series.pairing_add_series]
  calc
    _ ≤ |pairing g (orderedPowers (fun j => (P j).val) I)| +
        |pairing h (orderedPowers (fun j => (P j).val) I)| := abs_add_le _ _
    _ ≤ α * max C D ^ totalDegree I * (multiFactorial I : ℝ) +
        β * max C D ^ totalDegree I * (multiFactorial I : ℝ) := by
      apply add_le_add
      · refine (hb I).trans ?_
        gcongr
        exact le_max_left _ _
      · refine (hd I).trans ?_
        gcongr
        exact le_max_right _ _
    _ = _ := by ring

theorem holds_smul {X : Type} (a : ℝ) {g : NCSeries X} (hg : Holds g) :
    Holds (a • g) := by
  intro q P
  obtain ⟨α, hα, C, hC, hb⟩ := hg q P
  refine ⟨(|a| + 1) * α, by positivity, C, hC, ?_⟩
  intro I
  rw [Series.pairing_smul_series, abs_mul]
  calc
    _ ≤ (|a| + 1) * (α * C ^ totalDegree I * (multiFactorial I : ℝ)) := by
      apply mul_le_mul (by linarith [abs_nonneg a]) (hb I) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem holds_constant {X : Type} (a : ℝ) : Holds (constantSeries a : NCSeries X) := by
  let R : Representation X 0 := ⟨fun _ => Fin.elim0, MvPowerSeries.C a⟩
  have hR : Lax825748.AnalyticRepresentations.IsAnalytic R :=
    ⟨PowerSeriesBounds.convergent_C a, fun _ i => Fin.elim0 i⟩
  have he : generatingSeries R = constantSeries a :=
    (Lax825748.RepresentationMap.algebra_homomorphism R).1 a
  rw [← he]
  exact Lax825748.NecessaryConvergence.convergence R hR

theorem holds_letter_residual {X : Type} (g : NCSeries X) (hg : Holds g) (x : X) :
    Holds (Lax825748.Series.rightResidual g (letter x)) := by
  intro q P
  let L : LiePolynomial X := ⟨letter x,
    LieSubalgebra.subset_lieSpan (Set.mem_range_self x)⟩
  let P' : Fin (q + 1) → LiePolynomial X := Fin.cons L P
  obtain ⟨α, hα, C, hC, hb⟩ := hg (q + 1) P'
  refine ⟨α * C, mul_pos hα hC, C, hC, ?_⟩
  intro I
  rw [Series.pairing_right_residual]
  have he : orderedPowers (fun j => (P' j).val) (Fin.cons 1 I) =
      letter x * orderedPowers (fun j => (P j).val) I := by
    simp [orderedPowers, List.ofFn_succ, P', L]
  calc
    _ ≤ α * C ^ totalDegree (Fin.cons 1 I) * (multiFactorial (Fin.cons 1 I) : ℝ) := by
      simpa only [he] using hb (Fin.cons 1 I)
    _ = _ := by
      simp [totalDegree, multiFactorial, Fin.sum_univ_succ, Fin.prod_univ_succ,
        pow_add, mul_assoc]

theorem holds_word_residual {X : Type} (g : NCSeries X) (hg : Holds g) (w : Word X) :
    Holds (Lax825748.Series.rightResidual g (wordPolynomial w)) := by
  induction w using FreeMonoid.recOn generalizing g with
  | one =>
    have he : Lax825748.Series.rightResidual g (wordPolynomial 1) = g := by
      funext v
      simp
    rwa [he]
  | of_mul x w ih =>
    rw [Series.word_mul, ← Series.residual_mul]
    exact ih _ (holds_letter_residual g hg x)

/--
---
conclusion: Lax825748.ResidualConvergence.right_residual
---
Prepend a letter to the tested Lie family, with exponent one. Iteration
gives word residuals, and linearity gives every polynomial residual.
-/
theorem right_residual {X : Type} (g : NCSeries X) (hg : Holds g) (Q : NCPolynomial X) :
    Holds (Lax825748.Series.rightResidual g Q) := by
  induction Q using MonoidAlgebra.induction_on with
  | of w => exact holds_word_residual g hg w
  | add P Q hP hQ =>
    have he : Lax825748.Series.rightResidual g (P + Q) =
        Lax825748.Series.rightResidual g P + Lax825748.Series.rightResidual g Q := by
      funext w
      simp [Lax825748.Series.rightResidual, add_mul]
    rw [he]
    exact holds_add hP hQ
  | smul a P hP =>
    have he : Lax825748.Series.rightResidual g (a • P) =
        a • Lax825748.Series.rightResidual g P := by
      funext w
      simp [Lax825748.Series.rightResidual]
    rw [he]
    exact holds_smul a hP

/--
---
conclusion: Lax825748.ResidualConvergence.centered_residual
---
Subtracting the constant term preserves the convergence condition.
-/
theorem centered_residual {X : Type} (g : NCSeries X) (hg : Holds g) (Q : NCPolynomial X) :
    Holds (Lax825748.Series.rightResidual g Q - constantSeries (pairing g Q)) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (constantSeries (pairing g Q))]
  exact holds_add (Lax825748.ResidualConvergence.right_residual g hg Q)
    (holds_smul (-1) (holds_constant _))

end Lax825748Proofs.ResidualConvergence
