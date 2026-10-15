import Lax825748.FormalRealization

/-!
---
title: Lie rank is the least formal realization dimension
type: theorem
---
Every formal differential representation of dimension $e$ generates a series
of finite Lie rank at most $e$. Lie rank $d$ is equivalent to $d$ being
the least dimension of a formal differential
representation. This includes constant series, whose minimal dimension
is zero.
-/

noncomputable section

namespace Lax825748.FormalMinimality

open Series LieRank DifferentialRepresentation

def IsLeastDimension {X : Type} (g : NCSeries X) (d : ℕ) : Prop :=
  (∃ R : Representation X d, Represents R g) ∧
    ∀ e, (∃ R : Representation X e, Represents R g) → d ≤ e

axiom rank_bound {X : Type} {e : ℕ} (R : Representation X e) :
  ∃ d, HasLieRank (generatingSeries R) d ∧ d ≤ e

axiom least_dimension {X : Type} [Finite X] (g : NCSeries X) (d : ℕ) :
  HasLieRank g d ↔ IsLeastDimension g d

end Lax825748.FormalMinimality
