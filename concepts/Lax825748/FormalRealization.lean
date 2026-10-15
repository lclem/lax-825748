import Lax825748.DifferentialRepresentation
import Lax825748.Annihilator

/-!
---
title: FormalExistence of formal realizations
type: theorem
---
For a finite alphabet, a series admits a finite-dimensional formal differential
representation if and only if its Lie rank is finite. If it has Lie rank $d$,
a formal differential representation of dimension exactly $d$ exists.
-/

noncomputable section

namespace Lax825748.FormalRealization

open Series LieRank DifferentialRepresentation

axiom existence {X : Type} [Finite X] (g : NCSeries X) (d : ℕ)
    (hr : HasLieRank g d) :
  ∃ R : Representation X d, Represents R g

axiom characterization {X : Type} [Finite X] (g : NCSeries X) :
  DifferentiallyProduced g ↔ FiniteLieRank g

end Lax825748.FormalRealization
