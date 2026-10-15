import Lax825748.Shuffle
import Lax825748.LieRank
import Lax825748.Monomials
import Mathlib.Data.Fintype.Perm

/-!
---
title: Coproduct and shuffle identities
type: theorem
---
Lemmas 1–5. The $p$-fold coproduct assigns each position of a word to one
of $p$ tensor factors. Tensor polynomials are represented by finite linear
combinations of $p$-tuples of words. Its value on a letter is the sum of the
$p$ placements of that letter, and Lie polynomials are primitive.

Pairing with this coproduct computes the shuffle product. Letter residuals
are derivations. A shuffle product of $i$ zero-constant series vanishes on
a product of fewer than $i$ Lie polynomials. For equal numbers of factors,
the pairing is the sum over permutations of pairwise evaluations.

For normalized coordinate series, equal-degree monomials have diagonal
pairing $I!=\prod_i I_i!$ and off-diagonal pairing zero. This corrects
the printed $|I|!$ in Lemma 5(ii).
-/

noncomputable section

namespace Lax825748.ShuffleIdentities

open Series Shuffle LieRank Monomials
open scoped BigOperators

abbrev TensorPolynomial (X : Type) (p : ℕ) :=
  MonoidAlgebra ℝ (Fin p → Word X)

def distributions {X : Type} (p : ℕ) : List X → List (Fin p → List X)
  | [] => [fun _ => []]
  | x :: w => (distributions p w).flatMap fun v =>
      List.ofFn fun i : Fin p => Function.update v i (x :: v i)

noncomputable def coproduct {X : Type} (p : ℕ) (P : NCPolynomial X) :
    TensorPolynomial X p :=
  P.coeff.sum fun w a => ((distributions p w.toList).map fun v =>
    MonoidAlgebra.single (fun i => FreeMonoid.ofList (v i)) a).sum

noncomputable def tensorPairing {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (P : TensorPolynomial X p) : ℝ :=
  P.coeff.sum fun v a => a * ∏ i, S i (v i)

noncomputable def insertFactor {X : Type} {p : ℕ} (i : Fin p)
    (P : NCPolynomial X) : TensorPolynomial X p :=
  P.coeff.sum fun w a => MonoidAlgebra.single (fun j => if j = i then w else 1) a

axiom coproduct_multiplicative {X : Type} (p : ℕ) (P Q : NCPolynomial X) :
  coproduct p (P * Q) = coproduct p P * coproduct p Q

axiom pairing_coproduct {X : Type} {p : ℕ} (S : Fin p → NCSeries X)
    (P : NCPolynomial X) :
  pairing (shuffleList (List.ofFn S)) P = tensorPairing S (coproduct p P)

axiom lie_primitive {X : Type} (p : ℕ) (P : LiePolynomial X) :
  coproduct p P.val = ∑ i : Fin p, insertFactor i P.val

axiom residual_derivation {X : Type} (x : X) (S T : NCSeries X) :
  rightResidual (shuffle S T) (letter x) =
    shuffle (rightResidual S (letter x)) T + shuffle S (rightResidual T (letter x))

axiom vanishing {X : Type} {i j : ℕ} (hji : j < i)
    (T : Fin i → NCSeries X) (hT : ∀ k, T k 1 = 0)
    (Q : Fin j → LiePolynomial X) :
  pairing (shuffleList (List.ofFn T)) ((List.ofFn fun k => (Q k).val).prod) = 0

axiom permutation_pairing {X : Type} {n : ℕ}
    (T : Fin n → NCSeries X) (hT : ∀ k, T k 1 = 0)
    (Q : Fin n → LiePolynomial X) :
  pairing (shuffleList (List.ofFn T)) ((List.ofFn fun k => (Q k).val).prod) =
    ∑ σ : Equiv.Perm (Fin n), ∏ k, pairing (T k) (Q (σ k)).val

noncomputable def shuffleMonomial {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (I : Fin d → ℕ) : NCSeries X :=
  shuffleList (List.ofFn fun i => shufflePow (S i) (I i))

axiom triangular_pairing {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (P : Fin d → LiePolynomial X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (I J : Fin d → ℕ) :
  (totalDegree J < totalDegree I →
    pairing (shuffleMonomial S I) (orderedPowers (fun i => (P i).val) J) = 0) ∧
  (totalDegree I = totalDegree J →
    pairing (shuffleMonomial S I) (orderedPowers (fun i => (P i).val) J) =
      if I = J then (multiFactorial I : ℝ) else 0)

end Lax825748.ShuffleIdentities
