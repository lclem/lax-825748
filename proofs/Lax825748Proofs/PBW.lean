import Lax825748Proofs.PBWSpanning

noncomputable section

namespace Lax825748Proofs.PBW

open Lax825748.Series Lax825748.LieRank Lax825748.PBW

/--
---
conclusion: Lax825748.PBW.basis
---
Shuffle pairings separate the ordered monomials. Reordering adjacent basis
elements changes a product only by terms of lower Lie degree, which proves
spanning by induction on that degree.
-/
theorem basis {X ι : Type} [LinearOrder ι] (b : Module.Basis ι ℝ (LiePolynomial X)) :
    LinearIndependent ℝ (monomial b) ∧
      Submodule.span ℝ (Set.range (monomial b)) = ⊤ :=
  ⟨PBWIndependence.linearIndependent b, PBWSpanning.spanning b⟩

end Lax825748Proofs.PBW
