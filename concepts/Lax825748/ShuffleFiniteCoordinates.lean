import Lax825748.ShuffleFinite
import Lax825748.Annihilator
import Lax825748.RepresentationMap

/-!
---
title: Shuffle-finite coordinates in minimal formal realizations
type: theorem
---
If a shuffle-finite series has Lie rank $k$, its minimal formal realization
can be chosen with shuffle-finite coordinate series. They can lie in any
finitely generated, derivative-stable shuffle algebra containing the series.

For a complement $P_j$ to the residual stabilizer, choose polynomials $Q_i$
with $(f,Q_iP_j)=\delta_{ij}$. The coordinate series are
$g_i=f\circ Q_i-(f,Q_i)1$. They belong to the witnessing algebra and give
formal coordinates on the stabilizer ideal's annihilator. This does not
assert polynomial output or transition functions in these coordinates.
-/

noncomputable section

namespace Lax825748.ShuffleFiniteCoordinates

open Series ShuffleFinite LieRank Annihilator FormalSeries
open DifferentialRepresentation RepresentationMap

axiom coordinates_in_algebra {X : Type} {k : ℕ} (f : NCSeries X)
    (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A)
    (hstable : DerivativeStable A) (hf : f ∈ A.toSubmodule)
    (K : LieSubalgebraOfPolynomials X)
    (hK : ∀ L : LiePolynomial X, L ∈ K ↔ leftResidual L.val f = 0)
    (P : Fin k → LiePolynomial X) (hP : IsComplement K P) :
    ∃ (Q : Fin k → NCPolynomial X) (G : Fin k → NCSeries X),
      (∀ i, G i = rightResidual f (Q i) - constantSeries (pairing f (Q i))) ∧
      IsCoordinateFamily K P G ∧
      (∀ i, G i ∈ A.toSubmodule ∧ IsShuffleFinite (G i)) ∧
      (∀ T : NCSeries X, InAnnihilator K T ↔
        ∃! u : StateSeries k, substituteShuffle G u = T)

axiom minimal_realization {X : Type} [Finite X] (f : NCSeries X) (k : ℕ)
    (hr : HasLieRank f k) (A : ShuffleSubalgebra X)
    (hfg : FinitelyGenerated A) (hstable : DerivativeStable A) (hf : f ∈ A.toSubmodule) :
    ∃ R : Representation X k, Represents R f ∧
      ∀ i : Fin k, eta R (MvPowerSeries.X i) ∈ A.toSubmodule ∧
        IsShuffleFinite (eta R (MvPowerSeries.X i))

end Lax825748.ShuffleFiniteCoordinates
