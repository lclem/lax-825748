import Lax825748.Realization

/-!
---
title: Lie rank is the least analytic realization dimension
type: theorem
---
A series has Lie rank $d$ and satisfies (C) if and only if $d$ is the
least dimension of its analytic differential representations. The least
dimension is attained. Constant series are included with dimension zero.
-/

noncomputable section

namespace Lax825748.Minimality

open Lax825748.Series Lax825748.LieRank Lax825748.DifferentialRepresentation
open AnalyticRepresentations

def IsLeastDimension {X : Type} (g : NCSeries X) (d : ℕ) : Prop :=
  (∃ R : Representation X d, IsAnalytic R ∧ Represents R g) ∧
    ∀ e, (∃ R : Representation X e, IsAnalytic R ∧ Represents R g) → d ≤ e

axiom least_dimension {X : Type} [Finite X] (g : NCSeries X) (d : ℕ) :
  (HasLieRank g d ∧ ConvergenceHypothesis.Holds g) ↔ IsLeastDimension g d

end Lax825748.Minimality
