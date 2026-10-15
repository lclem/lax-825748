import Lax825748.FormalMinimality
import Lax825748.CoordinateChange
import Lax825748.Projection
import Lax825748.RepresentationMap

/-!
---
title: Formal equivalence of minimal realizations
type: theorem
---
Two formal differential representations of a series of Lie rank $d$, both of
dimension $d$, are equivalent under a formal change of coordinates
fixing the origin. The change sends the first output series to the second
and intertwines the right action of every word on every state series.
The change of coordinates and its inverse are continuous for the formal topology.
-/

noncomputable section

namespace Lax825748.FormalUniqueness

open Series LieRank DifferentialRepresentation CoordinateChange

axiom minimal_realizations_equivalent {X : Type} [Finite X] {d : ℕ}
    (g : NCSeries X) (hr : HasLieRank g d)
    (R R' : Representation X d) (hR : Represents R g) (hR' : Represents R' g) :
  ∃ φ : FormalChange d,
    φ.toAlgEquiv R.output = R'.output ∧
      ∀ (k : FormalSeries.StateSeries d) (w : Word X),
        φ.toAlgEquiv (act R k w) = act R' (φ.toAlgEquiv k) w

end Lax825748.FormalUniqueness
