import Lax825748.ConvergentSeries
import Lax825748.ConvergenceHypothesis
import Lax825748.Annihilator

/-!
---
title: Convergence of PBW coordinate expansions
type: theorem
---
Let $P_1,\ldots,P_d$ be a basis modulo a Lie subalgebra $L_0$, and let
$S_1,\ldots,S_d$ be the associated PBW coordinates of
$J^\perp$, where $J=\mathbb R\langle X\rangle L_0$.
If $T\in J^\perp$ satisfies (C), its coordinate expansion is convergent.
The coefficient of $S^I$ is $(T,P^I)/I!$, so (C) is precisely the
required geometric bound for this expansion.
-/

noncomputable section

namespace Lax825748.PBWConvergence

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.FormalSeries ConvergentSeries

axiom expansion_converges {X : Type} {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (S : Fin d → NCSeries X)
    (hS : IsCoordinateFamily K P S) (hPBW : IsPBWCoordinateFamily P S)
    (T : NCSeries X) (hT : InAnnihilator K T)
    (hC : ConvergenceHypothesis.Holds T) :
  ∃ f : StateSeries d, Convergent f ∧ substituteShuffle S f = T

end Lax825748.PBWConvergence
