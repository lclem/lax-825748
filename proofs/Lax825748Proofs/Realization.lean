import Lax825748.Minimality

noncomputable section

namespace Lax825748Proofs.Realization

open Lax208278.Series Lax208278.LieRank Lax208278.DifferentialRepresentation
open Lax825748.AnalyticRepresentations Lax825748.Minimality

/--
---
conclusion: Lax825748.Realization.characterization
---
Combine the formal rank bound, necessity of (C), and analytic existence in
the Lie-rank dimension.
-/
theorem characterization {X : Type} [Finite X] (g : NCSeries X) :
    AnalyticallyProduced g ↔ FiniteLieRank g ∧ Lax825748.ConvergenceHypothesis.Holds g := by
  constructor
  · rintro ⟨e, R, ha, hR⟩
    change generatingSeries R = g at hR
    obtain ⟨d, hd, _⟩ := Lax208278.Minimality.rank_bound R
    refine ⟨⟨d, ?_⟩, ?_⟩
    · simpa only [hR] using hd
    · simpa only [hR] using Lax825748.NecessaryConvergence.convergence R ha
  · rintro ⟨⟨d, hd⟩, hC⟩
    exact ⟨d, Lax825748.Realization.existence g d hd hC⟩

/--
---
conclusion: Lax825748.Minimality.least_dimension
---
Every analytic representation obeys the formal rank bound. Analytic
existence attains that bound, and necessity supplies (C).
-/
theorem least_dimension {X : Type} [Finite X] (g : NCSeries X) (d : ℕ) :
    (HasLieRank g d ∧ Lax825748.ConvergenceHypothesis.Holds g) ↔ IsLeastDimension g d := by
  constructor
  · rintro ⟨hd, hC⟩
    refine ⟨Lax825748.Realization.existence g d hd hC, ?_⟩
    rintro e ⟨R, _, hR⟩
    change generatingSeries R = g at hR
    obtain ⟨r, hr, hre⟩ := Lax208278.Minimality.rank_bound R
    have hrg : HasLieRank g r := by simpa only [hR] using hr
    have heq : d = r := hd.2.symm.trans hrg.2
    simpa only [heq] using hre
  · rintro ⟨⟨R, ha, hR⟩, hmin⟩
    change generatingSeries R = g at hR
    have hC : Lax825748.ConvergenceHypothesis.Holds g := by
      simpa only [hR] using Lax825748.NecessaryConvergence.convergence R ha
    obtain ⟨r, hr, hrd⟩ := Lax208278.Minimality.rank_bound R
    have hrg : HasLieRank g r := by simpa only [hR] using hr
    have hdr := hmin r (Lax825748.Realization.existence g r hrg hC)
    have heq : r = d := Nat.le_antisymm hrd hdr
    exact ⟨by simpa only [heq] using hrg, hC⟩

end Lax825748Proofs.Realization
