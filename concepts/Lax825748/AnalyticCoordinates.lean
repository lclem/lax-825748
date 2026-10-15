import Lax825748.PBWConvergence
import Lax825748.AnalyticCalculus
import Lax825748.AnalyticChanges

/-!
---
title: Convergent coordinates on an annihilator
type: theorem
---
Let $T_1,\ldots,T_d$ be normalized, zero-constant coordinates on $J^\perp$
as in Proposition 1, each satisfying (C). Every element of $J^\perp$
satisfying (C) is a convergent series in the $T_i$.

Indeed, the $T_i$ are convergent series in PBW coordinates and have
identity linear part. Their inverse change of coordinates is convergent
by the analytic inverse function theorem.
-/

noncomputable section

namespace Lax825748.AnalyticCoordinates

open Lax208278.Series Lax208278.LieRank Lax208278.Annihilator
open Lax208278.FormalSeries ConvergentSeries

axiom expansion_converges {X : Type} {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (T : Fin d → NCSeries X)
    (hT : IsCoordinateFamily K P T)
    (hCT : ∀ i, ConvergenceHypothesis.Holds (T i))
    (U : NCSeries X) (hU : InAnnihilator K U)
    (hCU : ConvergenceHypothesis.Holds U) :
  ∃ f : StateSeries d, Convergent f ∧ substituteShuffle T f = U

end Lax825748.AnalyticCoordinates
