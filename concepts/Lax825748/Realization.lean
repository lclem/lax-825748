import Lax825748.AnalyticRepresentations
import Lax825748.NecessaryConvergence
import Lax825748.ResidualConvergence
import Lax825748.AnalyticCoordinates
import Lax825748.FormalMinimality

/-!
---
title: Local analytic realization of generating series
type: theorem
---
For a finite alphabet, a real noncommutative series admits an analytic
differential representation if and only if it has finite Lie rank and
satisfies (C). If its Lie rank is $d$, a representation of dimension
exactly $d$ exists.

The realization is obtained in the normalized residual coordinates
$T_i=g\circ Q_i-(g,Q_i)$. Convergence of the output and of the vector-field
coefficients follows from their convergent coordinate expansions.
-/

noncomputable section

namespace Lax825748.Realization

open Lax825748.Series Lax825748.LieRank Lax825748.DifferentialRepresentation
open AnalyticRepresentations

axiom existence {X : Type} [Finite X] (g : NCSeries X) (d : ℕ)
    (hr : HasLieRank g d) (hC : ConvergenceHypothesis.Holds g) :
  ∃ R : Representation X d, IsAnalytic R ∧ Represents R g

axiom characterization {X : Type} [Finite X] (g : NCSeries X) :
  AnalyticallyProduced g ↔ FiniteLieRank g ∧ ConvergenceHypothesis.Holds g

end Lax825748.Realization
