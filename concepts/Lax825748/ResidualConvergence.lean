import Lax825748.ConvergenceHypothesis

/-!
---
title: Convergence under polynomial residuals
type: theorem
---
If $g$ satisfies (C), so do $g\circ Q$ and its centered series
$g\circ Q-(g,Q)$ for every noncommutative polynomial $Q$.
In particular the normalized observation coordinates used in part b)
and all their letter residuals satisfy (C).
-/

noncomputable section

namespace Lax825748.ResidualConvergence

open Lax208278.Series ConvergenceHypothesis

axiom right_residual {X : Type} (g : NCSeries X) (hg : Holds g)
    (Q : NCPolynomial X) :
  Holds (rightResidual g Q)

axiom centered_residual {X : Type} (g : NCSeries X) (hg : Holds g)
    (Q : NCPolynomial X) :
  Holds (rightResidual g Q - constantSeries (pairing g Q))

end Lax825748.ResidualConvergence
