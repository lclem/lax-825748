import Lax825748.FormalSeries

/-!
---
title: Convergent commutative power series
type: definition
---
A real power series in $d$ commuting variables is convergent if its
coefficients admit a geometric bound
$|f_I|\leq\alpha C^{|I|}$ with $\alpha,C>0$.
For finitely many variables this is equivalent to absolute convergence
on a neighborhood of the origin. Dimension zero is included.
-/

noncomputable section

namespace Lax825748.ConvergentSeries

open Lax825748.FormalSeries Lax825748.Monomials

def HasGeometricBound {d : ℕ} (f : StateSeries d) (α C : ℝ) : Prop :=
  ∀ I : Fin d →₀ ℕ, |MvPowerSeries.coeff I f| ≤ α * C ^ totalDegree I

def Convergent {d : ℕ} (f : StateSeries d) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ HasGeometricBound f α C

end Lax825748.ConvergentSeries
