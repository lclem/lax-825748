import Lax208278.LieRank
import Lax208278.Monomials

/-!
---
title: The convergence hypothesis on Lie polynomials
type: definition
---
Condition (C) requires that, for every finite ordered family of Lie
polynomials $P_1,\ldots,P_q$, there are $\alpha,C>0$ such that
$$|(g,P_1^{i_1}\cdots P_q^{i_q})|\leq\alpha C^{|I|}I!.$$
The constants may depend on the family, but not on the exponents.

The inequalities $I!\leq |I|!\leq q^{|I|}I!$ show that replacing $I!$
by $|I|!$ gives the same condition. Empty families are allowed.
-/

noncomputable section

namespace Lax825748.ConvergenceHypothesis

open Lax208278.Series Lax208278.LieRank Lax208278.Monomials

def Holds {X : Type} (g : NCSeries X) : Prop :=
  ∀ (q : ℕ) (P : Fin q → LiePolynomial X),
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧
      ∀ I : Fin q → ℕ,
        |pairing g (orderedPowers (fun j => (P j).val) I)| ≤
          α * C ^ totalDegree I * (multiFactorial I : ℝ)

def HoldsWithTotalFactorial {X : Type} (g : NCSeries X) : Prop :=
  ∀ (q : ℕ) (P : Fin q → LiePolynomial X),
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧
      ∀ I : Fin q → ℕ,
        |pairing g (orderedPowers (fun j => (P j).val) I)| ≤
          α * C ^ totalDegree I * ((totalDegree I).factorial : ℝ)

axiom factorial_comparison {q : ℕ} (I : Fin q → ℕ) :
  multiFactorial I ≤ (totalDegree I).factorial ∧
    (totalDegree I).factorial ≤ q ^ totalDegree I * multiFactorial I

axiom total_factorial_iff {X : Type} (g : NCSeries X) :
  Holds g ↔ HoldsWithTotalFactorial g

end Lax825748.ConvergenceHypothesis
