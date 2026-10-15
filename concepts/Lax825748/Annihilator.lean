import Lax825748.PBW
import Lax825748.ShuffleIdentities
import Lax825748.FormalSeries
import Mathlib.RingTheory.Ideal.Span

/-!
---
title: Formal coordinates on the annihilator of a Lie subalgebra
type: theorem
---
Proposition 1. Let $L_0$ be a Lie subalgebra of the Lie polynomials and let
$P_1,\ldots,P_d$ represent a basis modulo $L_0$. Set
$J=\mathbb R\langle X\rangle L_0$. If the zero-constant series $S_i$ vanish
on $J$ and satisfy $(S_i,P_j)=\delta_{ij}$, substitution of the $S_i$ into
commutative formal series is a bijection onto $J^\perp$.

Substitution is defined coefficient by coefficient using a finite truncation:
at a word of length $n$, only monomials of degree at most $n$ contribute.
There exist such coordinates dual to the degree-one PBW monomials. For these
coordinates the coefficient of $S^I$ in $T\in J^\perp$ is $(T,P^I)/I!$.
The annihilator is closed under the shuffle and all right residuals.
-/

noncomputable section

namespace Lax825748.Annihilator

open Series LieRank Monomials Shuffle ShuffleIdentities FormalSeries

abbrev LieSubalgebraOfPolynomials (X : Type) := LieSubalgebra ℝ (LiePolynomial X)

noncomputable def generatedIdeal {X : Type} (K : LieSubalgebraOfPolynomials X) :
    Ideal (NCPolynomial X) :=
  Ideal.span {P | ∃ k : K, P = k.val.val}

def InAnnihilator {X : Type} (K : LieSubalgebraOfPolynomials X) (S : NCSeries X) : Prop :=
  ∀ P ∈ generatedIdeal K, pairing S P = 0

def IsComplement {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) : Prop :=
  LinearIndependent ℝ (fun i => K.toSubmodule.mkQ (P i)) ∧
    Submodule.span ℝ (Set.range fun i => K.toSubmodule.mkQ (P i)) = ⊤

def IsCoordinateFamily {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (S : Fin d → NCSeries X) : Prop :=
  (∀ i, S i 1 = 0) ∧ (∀ i, InAnnihilator K (S i)) ∧
    ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0

noncomputable def substituteShuffle {X : Type} {d : ℕ}
    (S : Fin d → NCSeries X) (f : StateSeries d) : NCSeries X :=
  fun w => (AddMonoidAlgebra.coeff
    (MvPowerSeries.truncTotal (w.toList.length + 1) f)).sum
    fun I a => a * shuffleMonomial S I w

def IsPBWCoordinateFamily {X : Type} {d : ℕ}
    (P : Fin d → LiePolynomial X) (S : Fin d → NCSeries X) : Prop :=
  ∀ i (I : Fin d →₀ ℕ),
    pairing (S i) (orderedPowers (fun j => (P j).val) I) =
      if I = Finsupp.single i 1 then 1 else 0

axiom coordinates_exist {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P) :
  ∃ S : Fin d → NCSeries X, IsCoordinateFamily K P S ∧ IsPBWCoordinateFamily P S

axiom formal_coordinates {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S) :
  ∀ T : NCSeries X, InAnnihilator K T ↔ ∃! f : StateSeries d, substituteShuffle S f = T

axiom pbw_expansion {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S)
    (hPBW : IsPBWCoordinateFamily P S) (T : NCSeries X) (hT : InAnnihilator K T) :
  ∃ f : StateSeries d, substituteShuffle S f = T ∧
    ∀ I : Fin d →₀ ℕ, MvPowerSeries.coeff I f =
      pairing T (orderedPowers (fun j => (P j).val) I) / (multiFactorial I : ℝ)

axiom closed_shuffle {X : Type} (K : LieSubalgebraOfPolynomials X)
    (S T : NCSeries X) (hS : InAnnihilator K S) (hT : InAnnihilator K T) :
  InAnnihilator K (shuffle S T)

axiom closed_residual {X : Type} (K : LieSubalgebraOfPolynomials X)
    (S : NCSeries X) (hS : InAnnihilator K S) (P : NCPolynomial X) :
  InAnnihilator K (rightResidual S P)

end Lax825748.Annihilator
