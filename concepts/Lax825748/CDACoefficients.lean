import Lax825748.CDA
import Lax825748.ShuffleFiniteCoordinates

/-!
---
title: CDA coefficients in minimal formal realizations
type: theorem
---
In normalized shuffle-finite coordinates, all elements of the witnessing
shuffle algebra that belong to the coordinate annihilator have expansions
in one finitely generated algebra stable under ordinary partial derivatives.
In particular, a minimal realization has CDA output and CDA vector-field
coefficients, while its coordinate series remain shuffle finite.
-/

noncomputable section

namespace Lax825748.CDACoefficients

open Series LieRank Annihilator FormalSeries ShuffleFinite
open DifferentialRepresentation RepresentationMap CDA

axiom coordinate_algebra {X : Type} {k : ℕ}
    (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A)
    (hstable : ShuffleFinite.DerivativeStable A)
    (K : LieSubalgebraOfPolynomials X) (P : Fin k → LiePolynomial X)
    (hP : IsComplement K P) (G : Fin k → NCSeries X)
    (hG : IsCoordinateFamily K P G) (hmem : ∀ i, G i ∈ A.toSubmodule) :
    ∃ C : Subalgebra ℝ (StateSeries k), C.FG ∧ CDA.DerivativeStable C ∧
      ∀ u : StateSeries k, substituteShuffle G u ∈ A.toSubmodule → u ∈ C

axiom minimal_realization {X : Type} [Finite X] (f : NCSeries X) (k : ℕ)
    (hr : HasLieRank f k) (A : ShuffleSubalgebra X)
    (hfg : FinitelyGenerated A) (hstable : ShuffleFinite.DerivativeStable A)
    (hf : f ∈ A.toSubmodule) :
    ∃ R : Representation X k, Represents R f ∧ IsCDA R.output ∧
      (∀ (x : X) (i : Fin k), IsCDA (R.fields x i)) ∧
      ∀ i : Fin k, eta R (MvPowerSeries.X i) ∈ A.toSubmodule ∧
        IsShuffleFinite (eta R (MvPowerSeries.X i))

end Lax825748.CDACoefficients
