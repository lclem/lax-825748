import Lax825748.AnalyticRepresentations

/-!
---
title: Factorial estimates for iterated analytic vector fields
type: theorem
---
Suppose the output and all vector-field coefficients admit the same bound
$\alpha C^{|I|}$, where $\alpha,C>0$. For a word of length $p$, its generated
coefficient has absolute value at most $\alpha(2d\alpha C)^p p!$.
Consequently every analytic representation on a finite alphabet has a
uniform factorial bound on its word coefficients.

The central binomial estimate used in the majorant calculation is
$\binom{2p}{p}\leq 4^p$, rather than the printed $2^p$.
-/

noncomputable section

namespace Lax825748.FactorialEstimate

open Lax825748.Series Lax825748.DifferentialRepresentation
open ConvergentSeries AnalyticRepresentations

def HasFactorialBound {X : Type} (g : NCSeries X) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∀ w : Word X,
    |g w| ≤ α * C ^ w.toList.length * (w.toList.length.factorial : ℝ)

axiom word_majorant {X : Type} {d : ℕ} (R : Representation X d)
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C)
    (hh : HasGeometricBound R.output α C)
    (hA : ∀ x i, HasGeometricBound (R.fields x i) α C) (w : Word X) :
  |generatingSeries R w| ≤
    α * (2 * (d : ℝ) * α * C) ^ w.toList.length * (w.toList.length.factorial : ℝ)

axiom factorial_bound {X : Type} [Finite X] {d : ℕ}
    (R : Representation X d) (hR : IsAnalytic R) :
  HasFactorialBound (generatingSeries R)

end Lax825748.FactorialEstimate
