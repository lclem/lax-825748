import Lax825748.Minimality
import Lax825748.AnalyticChanges
import Lax208278.Uniqueness

/-!
---
title: Analytic equivalence of minimal realizations
type: theorem
---
Two analytic differential representations of a series of Lie rank $d$,
both of dimension $d$, are related by an analytic change of coordinates
fixing the origin. This change sends the first output to the second and
intertwines the action of every word on every state series.
Its inverse is also convergent and formally continuous.
-/

noncomputable section

namespace Lax825748.Uniqueness

open Lax208278.Series Lax208278.LieRank Lax208278.FormalSeries
open Lax208278.DifferentialRepresentation AnalyticRepresentations AnalyticChanges

axiom minimal_realizations_equivalent {X : Type} [Finite X] {d : ℕ}
    (g : NCSeries X) (hr : HasLieRank g d)
    (R R' : Representation X d) (hR : Represents R g) (hR' : Represents R' g)
    (ha : IsAnalytic R) (ha' : IsAnalytic R') :
  ∃ φ : AnalyticChange d,
    φ.toAlgEquiv R.output = R'.output ∧
      ∀ (k : StateSeries d) (w : Word X),
        φ.toAlgEquiv (act R k w) = act R' (φ.toAlgEquiv k) w

end Lax825748.Uniqueness
