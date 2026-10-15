import Lax825748.FormalSeries
import Mathlib.RingTheory.Adjoin.FG

/-!
---
title: Constructible differentially algebraic series
type: definition
---
A commutative formal power series is constructible differentially algebraic
(CDA) if it belongs to a finitely generated unital real subalgebra stable
under every ordinary partial derivative. Auxiliary generators are allowed;
their number need not equal the number of independent variables.
-/

noncomputable section

namespace Lax825748.CDA

open FormalSeries

def DerivativeStable {d : ℕ} (C : Subalgebra ℝ (StateSeries d)) : Prop :=
  ∀ (i : Fin d) (f : StateSeries d), f ∈ C → MvPowerSeries.pderiv ℝ i f ∈ C

def IsCDA {d : ℕ} (f : StateSeries d) : Prop :=
  ∃ C : Subalgebra ℝ (StateSeries d), C.FG ∧ DerivativeStable C ∧ f ∈ C

end Lax825748.CDA
