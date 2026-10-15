import Lax825748.DifferentialRepresentation
import Lax825748.Shuffle

/-!
---
title: The series homomorphism of a differential representation
type: theorem
---
Lemma 6. The map $\eta(k)_w=(k\mu w)(0)$ is a formally continuous real
algebra homomorphism from the state series to the shuffle series, and
$\eta(k\mu w)=\eta(k)\circ w$.
Algebra preservation is expressed by its scalar, additive, and multiplicative
identities, with shuffle multiplication written explicitly.
-/

noncomputable section

namespace Lax825748.RepresentationMap

open Series FormalSeries DifferentialRepresentation Shuffle

noncomputable def eta {X : Type} {d : ℕ} (R : Representation X d)
    (k : StateSeries d) : NCSeries X :=
  fun w => MvPowerSeries.constantCoeff (act R k w)

axiom algebra_homomorphism {X : Type} {d : ℕ} (R : Representation X d) :
  (∀ a : ℝ, eta R (MvPowerSeries.C a) = constantSeries a) ∧
  (∀ f k, eta R (f + k) = eta R f + eta R k) ∧
  (∀ f k, eta R (f * k) = shuffle (eta R f) (eta R k))

axiom continuous {X : Type} {d : ℕ} (R : Representation X d) :
  ∀ N, ∃ M, ∀ f k, FormalSeries.AgreeBelow M f k →
    Series.AgreeBelow N (eta R f) (eta R k)

axiom intertwining {X : Type} {d : ℕ} (R : Representation X d)
    (k : StateSeries d) (w : Word X) :
  eta R (act R k w) = rightResidual (eta R k) (wordPolynomial w)

end Lax825748.RepresentationMap
