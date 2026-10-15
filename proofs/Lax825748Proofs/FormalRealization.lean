import Lax825748.FormalMinimality

noncomputable section

namespace Lax825748Proofs.FormalRealization

open Lax825748.Series Lax825748.LieRank Lax825748.DifferentialRepresentation
open Lax825748.FormalMinimality

/--
---
conclusion: Lax825748.FormalRealization.characterization
---
FormalExistence in the Lie-rank dimension and the general rank bound give the two
directions of the characterization.
-/
theorem characterization {X : Type} [Finite X] (g : NCSeries X) :
    DifferentiallyProduced g ↔ FiniteLieRank g := by
  constructor
  · rintro ⟨e, R, hR⟩
    change generatingSeries R = g at hR
    obtain ⟨d, hd, _⟩ := rank_bound R
    exact ⟨d, by simpa only [hR] using hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, Lax825748.FormalRealization.existence g d hd⟩

/--
---
conclusion: Lax825748.FormalMinimality.least_dimension
---
The rank bound applies to every representation, while existence attains it.
-/
theorem least_dimension {X : Type} [Finite X] (g : NCSeries X) (d : ℕ) :
    HasLieRank g d ↔ IsLeastDimension g d := by
  constructor
  · intro hd
    refine ⟨Lax825748.FormalRealization.existence g d hd, ?_⟩
    rintro e ⟨R, hR⟩
    change generatingSeries R = g at hR
    obtain ⟨r, hr, hre⟩ := rank_bound R
    have hrg : HasLieRank g r := by simpa only [hR] using hr
    have heq : d = r := hd.2.symm.trans hrg.2
    simpa only [heq] using hre
  · rintro ⟨⟨R, hR⟩, hmin⟩
    change generatingSeries R = g at hR
    obtain ⟨r, hr, hrd⟩ := rank_bound R
    have hrg : HasLieRank g r := by simpa only [hR] using hr
    have hdr := hmin r (Lax825748.FormalRealization.existence g r hrg)
    have heq : r = d := Nat.le_antisymm hrd hdr
    simpa only [heq] using hrg

end Lax825748Proofs.FormalRealization
