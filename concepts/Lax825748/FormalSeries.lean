import Lax825748.Monomials
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
---
title: Commutative formal series and formal vector fields
type: definition
---
The state algebra in dimension $d$ is $\mathbb R[[q_1,\ldots,q_d]]$.
Its elements are arbitrary commutative formal power series.

A formal vector field with coefficients $\theta_i$ acts on $f$ by
$\sum_i\theta_i\partial_i f$. Formal continuity means continuity for the topology of
agreement of all coefficients below a fixed total degree.
-/

noncomputable section

namespace Lax825748.FormalSeries

open Monomials
open scoped BigOperators

abbrev StateSeries (d : ℕ) := MvPowerSeries (Fin d) ℝ

def AgreeBelow {d : ℕ} (N : ℕ) (f g : StateSeries d) : Prop :=
  ∀ I : Fin d →₀ ℕ, totalDegree I < N →
    MvPowerSeries.coeff I f = MvPowerSeries.coeff I g

def FormallyContinuous {d e : ℕ} (F : StateSeries d → StateSeries e) : Prop :=
  ∀ N, ∃ M, ∀ f g, AgreeBelow M f g → AgreeBelow N (F f) (F g)

abbrev VectorField (d : ℕ) := Fin d → StateSeries d

noncomputable def applyVectorField {d : ℕ} (A : VectorField d)
    (f : StateSeries d) : StateSeries d :=
  ∑ i, A i * MvPowerSeries.pderiv ℝ i f

end Lax825748.FormalSeries
