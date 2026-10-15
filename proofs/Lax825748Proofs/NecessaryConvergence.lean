import Lax825748.NecessaryConvergence
import Lax825748Proofs.PowerSeriesBounds
import Lax825748Proofs.Rank
import Lax825748Proofs.ContinuousDerivations
import Lax825748Proofs.MonomialLists

noncomputable section

namespace Lax825748Proofs.NecessaryConvergence

open Lax825748.Series Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.LieRank Lax825748.Monomials
open Lax825748.ConvergentSeries Lax825748.AnalyticRepresentations
open Lax825748Proofs Operators MonomialLists
open PowerSeriesBounds
open scoped BigOperators

theorem field_convergent {d : ℕ} (A : VectorField d) (hA : ∀ i, Convergent (A i))
    (f : StateSeries d) (hf : Convergent f) : Convergent (applyVectorField A f) := by
  obtain ⟨B, hB⟩ := Lax825748.AnalyticCalculus.subalgebra d
  apply (hB _).mp
  apply B.sum_mem
  intro i _
  apply B.mul_mem ((hB _).mpr (hA i))
  exact (hB _).mpr (Lax825748.AnalyticCalculus.partial_derivative f hf i)

theorem act_convergent {X : Type} {d : ℕ} (R : Representation X d)
    (hR : ∀ x i, Convergent (R.fields x i)) (f : StateSeries d)
    (hf : Convergent f) (w : Word X) : Convergent (act R f w) := by
  induction w using FreeMonoid.recOn generalizing f with
  | one => exact hf
  | of_mul x w ih =>
    exact ih _ (field_convergent _ (hR x) f hf)

theorem operator_convergent {X : Type} {d : ℕ} (R : Representation X d)
    (hR : ∀ x i, Convergent (R.fields x i)) (Q : NCPolynomial X)
    (f : StateSeries d) (hf : Convergent f) : Convergent (operator R Q f) := by
  induction Q using MonoidAlgebra.induction_on with
  | of w =>
    change Convergent (operator R (wordPolynomial w) f)
    rw [operator_word]
    exact act_convergent R hR f hf w
  | add P Q hP hQ =>
    simpa only [map_add, LinearMap.add_apply] using convergent_add hP hQ
  | smul a P hP =>
    simpa only [map_smul, LinearMap.smul_apply] using convergent_smul a hP

theorem induced_action {X : Type} {d q : ℕ} (R : Representation X d)
    (P : Fin q → LiePolynomial X) (A : Fin q → VectorField d)
    (hA : ∀ j f, operator R (P j).val f = applyVectorField (A j) f)
    (f : StateSeries d) (w : Word (Fin q)) :
    act (⟨A, R.output⟩ : Representation (Fin q) d) f w =
      operator R ((w.toList.map fun j => (P j).val).prod) f := by
  induction w using FreeMonoid.recOn generalizing f with
  | one =>
    change f = operator R 1 f
    have h1 : (1 : NCPolynomial X) = wordPolynomial 1 := rfl
    rw [h1, operator_word]
    rfl
  | of_mul j w ih =>
    change act (⟨A, R.output⟩ : Representation (Fin q) d)
      (applyVectorField (A j) f) w =
        operator R ((P j).val * (w.toList.map fun k => (P k).val).prod) f
    rw [ih, operator_mul, Module.End.mul_apply, hA]

/--
---
conclusion: Lax825748.NecessaryConvergence.convergence
---
Every finite family of Lie polynomials acts by convergent vector fields.
Apply the factorial estimate to this finite alphabet, then compare the
total factorial with the multi-index factorial.
-/
theorem convergence {X : Type} {d : ℕ} (R : Representation X d)
    (hR : IsAnalytic R) : Lax825748.ConvergenceHypothesis.Holds (generatingSeries R) := by
  apply (Lax825748.ConvergenceHypothesis.total_factorial_iff _).mpr
  intro q P
  choose A hA using fun j => lie_operator_field R (P j)
  let R' : Representation (Fin q) d := ⟨A, R.output⟩
  have hR' : IsAnalytic R' := by
    refine ⟨hR.1, ?_⟩
    intro j i
    have hc := operator_convergent R hR.2 (P j).val (MvPowerSeries.X i) (convergent_X i)
    rwa [hA, ContinuousDerivations.field_X] at hc
  obtain ⟨α, hα, C, hC, hb⟩ := Lax825748.FactorialEstimate.factorial_bound R' hR'
  refine ⟨α, hα, C, hC, ?_⟩
  intro I
  let w : Word (Fin q) := FreeMonoid.ofList (labelsList I)
  have hw : w.toList.length = totalDegree I := labelsList_length I
  have hp : (w.toList.map fun j => (P j).val).prod =
      orderedPowers (fun j => (P j).val) I := by
    rw [labels_polynomial]
    change ((labelsList I).map _).prod = _
    rw [← ofFn_labels]
    simp [List.map_ofFn, Function.comp_def]
  have he : generatingSeries R' w =
      pairing (generatingSeries R) (orderedPowers (fun j => (P j).val) I) := by
    change MvPowerSeries.constantCoeff (act R' R.output w) =
      pairing (Lax825748.RepresentationMap.eta R R.output) _
    rw [Rank.pairing_operator]
    congr 1
    rw [show R' = (⟨A, R.output⟩ : Representation (Fin q) d) from rfl,
      induced_action R P A hA, hp]
  simpa only [hw, he] using hb w

end Lax825748Proofs.NecessaryConvergence
