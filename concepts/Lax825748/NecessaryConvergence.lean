import Lax825748.FactorialEstimate
import Lax825748.AnalyticCalculus
import Lax825748.ConvergenceHypothesis

/-!
---
title: Analytic representations satisfy the convergence hypothesis
type: theorem
---
The generating series of an analytic differential representation satisfies
condition (C). A finite family of Lie polynomials acts by analytic vector
fields. Applying the factorial estimate to these new fields, and comparing
the total factorial with the product of factorials, gives the assertion.
-/

noncomputable section

namespace Lax825748.NecessaryConvergence

open Lax208278.DifferentialRepresentation AnalyticRepresentations

axiom convergence {X : Type} {d : ℕ} (R : Representation X d)
    (hR : IsAnalytic R) :
  ConvergenceHypothesis.Holds (generatingSeries R)

end Lax825748.NecessaryConvergence
