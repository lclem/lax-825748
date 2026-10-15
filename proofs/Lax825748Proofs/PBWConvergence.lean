import Lax825748.PBWConvergence
import Mathlib.Tactic

noncomputable section

namespace Lax825748Proofs.PBWConvergence

open Lax208278.Series Lax208278.LieRank Lax208278.Annihilator
open Lax208278.FormalSeries Lax208278.Monomials Lax825748.ConvergentSeries

/--
---
conclusion: Lax825748.PBWConvergence.expansion_converges
---
The PBW coefficient formula divides the bound in (C) by the positive
multi-index factorial, leaving a geometric coefficient bound.
-/
theorem expansion_converges {X : Type} {d : ℕ}
    (K : LieSubalgebraOfPolynomials X) (P : Fin d → LiePolynomial X)
    (hP : IsComplement K P) (S : Fin d → NCSeries X)
    (hS : IsCoordinateFamily K P S) (hPBW : IsPBWCoordinateFamily P S)
    (T : NCSeries X) (hT : InAnnihilator K T)
    (hC : Lax825748.ConvergenceHypothesis.Holds T) :
    ∃ f : StateSeries d, Convergent f ∧ substituteShuffle S f = T := by
  obtain ⟨f, hf, hc⟩ := Lax208278.Annihilator.pbw_expansion K P hP S hS hPBW T hT
  obtain ⟨α, hα, C, hCpos, hbound⟩ := hC d P
  refine ⟨f, ⟨α, hα, C, hCpos, ?_⟩, hf⟩
  intro I
  have hfac : (0 : ℝ) < multiFactorial I := by
    exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos (I i))
  rw [hc I, abs_div, abs_of_pos hfac]
  exact (div_le_iff₀ hfac).mpr (hbound I)

end Lax825748Proofs.PBWConvergence
