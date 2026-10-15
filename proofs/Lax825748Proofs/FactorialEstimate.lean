import Lax825748.FactorialEstimate
import Lax825748Proofs.PowerSeriesBounds

noncomputable section

namespace Lax825748Proofs.FactorialEstimate

open Lax208278.Series Lax208278.FormalSeries Lax208278.DifferentialRepresentation
open Lax825748.ConvergentSeries Lax825748.AnalyticRepresentations Lax825748.FactorialEstimate

/--
---
conclusion: Lax825748.FactorialEstimate.factorial_bound
---
Choose one geometric coefficient bound for the output and the finitely
many vector-field coefficients, and apply the word majorant.
-/
theorem factorial_bound {X : Type} [Finite X] {d : ℕ}
    (R : Representation X d) (hR : IsAnalytic R) :
    HasFactorialBound (generatingSeries R) := by
  classical
  let := Fintype.ofFinite X
  let f : Option (X × Fin d) → StateSeries d
    | none => R.output
    | some p => R.fields p.1 p.2
  have hf : ∀ i, Convergent (f i) := by
    rintro (_ | ⟨x, i⟩)
    · exact hR.1
    · exact hR.2 x i
  obtain ⟨α, hα, C, hC, hb⟩ := PowerSeriesBounds.common_bounds f hf
  refine ⟨α, hα, max 1 (2 * (d : ℝ) * α * C), lt_max_iff.mpr (.inl (by norm_num)), ?_⟩
  intro w
  refine (Lax825748.FactorialEstimate.word_majorant R α C hα hC
    (hb none) (fun x i => hb (some (x, i))) w).trans ?_
  gcongr
  exact le_max_right _ _

end Lax825748Proofs.FactorialEstimate
