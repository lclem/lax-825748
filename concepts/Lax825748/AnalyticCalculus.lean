import Lax825748.ConvergentSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
---
title: Calculus of convergent power series
type: theorem
---
The geometric coefficient bound is equivalent to absolute summability at
some positive polyradius. Convergent series form a real subalgebra and are
closed under partial differentiation.

A formally continuous algebra homomorphism sending each variable to a
convergent series with zero constant term preserves convergence. This is
composition of convergent power series at the origin.
-/

noncomputable section

namespace Lax825748.AnalyticCalculus

open Lax208278.FormalSeries Lax208278.Monomials ConvergentSeries

axiom absolute_convergence {d : ℕ} (f : StateSeries d) :
  Convergent f ↔ ∃ r : ℝ, 0 < r ∧
    Summable (fun I : Fin d →₀ ℕ => |MvPowerSeries.coeff I f| * r ^ totalDegree I)

axiom subalgebra (d : ℕ) :
  ∃ A : Subalgebra ℝ (StateSeries d), ∀ f, f ∈ A ↔ Convergent f

axiom partial_derivative {d : ℕ} (f : StateSeries d) (hf : Convergent f)
    (i : Fin d) :
  Convergent (MvPowerSeries.pderiv ℝ i f)

axiom composition {d e : ℕ} (φ : StateSeries d →ₐ[ℝ] StateSeries e)
    (hc : FormallyContinuous φ)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ (MvPowerSeries.X i)) = 0)
    (hφ : ∀ i, Convergent (φ (MvPowerSeries.X i)))
    (f : StateSeries d) (hf : Convergent f) :
  Convergent (φ f)

end Lax825748.AnalyticCalculus
