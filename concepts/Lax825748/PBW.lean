import Lax825748.LieRank
import Mathlib.LinearAlgebra.Basis.Defs

/-!
---
title: Poincaré–Birkhoff–Witt for Lie polynomials
type: theorem
---
Given any totally ordered basis of the Lie polynomials, the nondecreasing
products of its basis elements, including the empty product, form a basis
of the concatenation algebra $\mathbb R\langle X\rangle$.
Linear independence and spanning are stated separately in the conjunction.
-/

noncomputable section

namespace Lax825748.PBW

open Series LieRank

abbrev OrderedWord (ι : Type) [LinearOrder ι] :=
  {l : List ι // l.Pairwise (· ≤ ·)}

noncomputable def monomial {X ι : Type} [LinearOrder ι]
    (b : Module.Basis ι ℝ (LiePolynomial X)) (l : OrderedWord ι) : NCPolynomial X :=
  (l.val.map fun i => (b i).val).prod

axiom basis {X ι : Type} [LinearOrder ι] (b : Module.Basis ι ℝ (LiePolynomial X)) :
  LinearIndependent ℝ (monomial b) ∧
    Submodule.span ℝ (Set.range (monomial b)) = ⊤

end Lax825748.PBW
