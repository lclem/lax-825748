import Lax825748.ConvergentSeries
import Lax208278.DifferentialRepresentation

/-!
---
title: Analytic differential representations
type: definition
---
A differential representation is analytic if its output series and every
coefficient of each of its vector fields converge near the origin.
Its generated coefficient at a word $w$ is the constant term of $h\mu w$,
with the vector fields acting on the right in the order of the letters.
A series is analytically produced if such a representation exists in some
finite dimension, including dimension zero.

Convergence of the vector fields is required explicitly. It is used in
the proof and in the interpretation by analytic systems, although omitted
from the printed Definition 1.
-/

noncomputable section

namespace Lax825748.AnalyticRepresentations

open Lax208278.Series Lax208278.DifferentialRepresentation ConvergentSeries

def IsAnalytic {X : Type} {d : ℕ} (R : Representation X d) : Prop :=
  Convergent R.output ∧ ∀ x i, Convergent (R.fields x i)

def AnalyticallyProduced {X : Type} (g : NCSeries X) : Prop :=
  ∃ d, ∃ R : Representation X d, IsAnalytic R ∧ Represents R g

end Lax825748.AnalyticRepresentations
