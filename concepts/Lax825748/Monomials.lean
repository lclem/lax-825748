import Lax825748.Series
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
---
title: Multi-indices and ordered monomials
type: definition
---
For a multi-index $I=(i_1,\ldots,i_d)$, write $|I|=\sum_j i_j$ and
$I!=\prod_j i_j!$. For an ordered family of noncommutative polynomials,
$P^I=P_1^{i_1}\cdots P_d^{i_d}$ uses that order of multiplication.
The empty family has total degree zero, factorial one, and monomial one.
-/

noncomputable section

namespace Lax825748.Monomials

open Series
open scoped BigOperators

def totalDegree {d : ℕ} (I : Fin d → ℕ) : ℕ := ∑ j, I j

def multiFactorial {d : ℕ} (I : Fin d → ℕ) : ℕ := ∏ j, (I j).factorial

noncomputable def orderedPowers {X : Type} {d : ℕ}
    (P : Fin d → NCPolynomial X) (I : Fin d → ℕ) : NCPolynomial X :=
  (List.ofFn fun j => P j ^ I j).prod

end Lax825748.Monomials
