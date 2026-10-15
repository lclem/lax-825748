import Lax825748.Annihilator

/-!
---
title: The PBW coordinate projection
type: theorem
---
Lemma 7. For the PBW coordinates of a finite-codimension Lie subalgebra,
$$\theta(T)=\sum_I\frac{(T,P^I)}{I!}S^I$$
is a formally continuous shuffle algebra homomorphism. It maps onto
$J^\perp$ and is the identity there.
-/

noncomputable section

namespace Lax825748.Projection

open Series LieRank Monomials Shuffle FormalSeries Annihilator

noncomputable def theta {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (T : NCSeries X) : NCSeries X :=
  substituteShuffle S (fun I =>
    pairing T (orderedPowers (fun j => (P j).val) I) / (multiFactorial I : ℝ))

axiom projection {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S)
    (hPBW : IsPBWCoordinateFamily P S) :
  Series.FormallyContinuous (theta P S) ∧
  (∀ a : ℝ, theta P S (constantSeries a) = constantSeries a) ∧
  (∀ T U, theta P S (T + U) = theta P S T + theta P S U) ∧
  (∀ T U, theta P S (shuffle T U) = shuffle (theta P S T) (theta P S U)) ∧
  (∀ T, InAnnihilator K (theta P S T)) ∧
  (∀ T, InAnnihilator K T → theta P S T = T)

end Lax825748.Projection
