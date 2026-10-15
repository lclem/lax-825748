import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Real.Basic

/-!
---
title: Noncommutative series and polynomial residuals
type: definition
---
For an alphabet $X$, a series is a function $X^*\to\mathbb R$ and a polynomial
is a finite real linear combination of words. Polynomial multiplication is
concatenation. The pairing is $(S,P)=\sum_w P_w S_w$.

The two residuals are $(S\circ P,w)=(S,Pw)$ and
$(P\circ S,w)=(S,wP)$. The empty word is the monoid identity.
Agreement below degree $N$ means equality at every word of length less than $N$.
-/

noncomputable section

namespace Lax825748.Series

abbrev Word (X : Type) := FreeMonoid X
abbrev NCSeries (X : Type) := Word X → ℝ
abbrev NCPolynomial (X : Type) := MonoidAlgebra ℝ (Word X)

noncomputable def pairing {X : Type} (S : NCSeries X) (P : NCPolynomial X) : ℝ :=
  P.coeff.sum fun w a => a * S w

noncomputable def wordPolynomial {X : Type} (w : Word X) : NCPolynomial X :=
  MonoidAlgebra.single w 1

noncomputable def letter {X : Type} (x : X) : NCPolynomial X :=
  wordPolynomial (FreeMonoid.of x)

noncomputable def rightResidual {X : Type} (S : NCSeries X)
    (P : NCPolynomial X) : NCSeries X :=
  fun w => pairing S (P * wordPolynomial w)

noncomputable def leftResidual {X : Type} (P : NCPolynomial X)
    (S : NCSeries X) : NCSeries X :=
  fun w => pairing S (wordPolynomial w * P)

noncomputable def constantSeries {X : Type} (a : ℝ) : NCSeries X := by
  classical
  exact fun w => if w = 1 then a else 0

def AgreeBelow {X : Type} (N : ℕ) (S T : NCSeries X) : Prop :=
  ∀ w, w.toList.length < N → S w = T w

def FormallyContinuous {X Y : Type} (F : NCSeries X → NCSeries Y) : Prop :=
  ∀ N, ∃ M, ∀ S T, AgreeBelow M S T → AgreeBelow N (F S) (F T)

end Lax825748.Series
