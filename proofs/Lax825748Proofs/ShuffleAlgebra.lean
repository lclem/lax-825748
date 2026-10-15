import Lax825748Proofs.SubstitutionFinite

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Lax825748Proofs.ShuffleAlgebra

open Lax825748.Series Lax825748.Shuffle Lax825748.ShuffleIdentities
open scoped BigOperators

def Algebra (X : Type) := NCSeries X

instance {X : Type} : AddCommGroup (Algebra X) := inferInstanceAs (AddCommGroup (NCSeries X))
instance {X : Type} : Module ℝ (Algebra X) := inferInstanceAs (Module ℝ (NCSeries X))

instance {X : Type} : CommRing (Algebra X) where
  __ := (inferInstance : AddCommGroup (Algebra X))
  one := constantSeries 1
  mul := shuffle
  mul_assoc := Shuffle.associative
  one_mul := Shuffle.unit
  mul_one S := (Shuffle.commutative S _).trans (Shuffle.unit S)
  mul_comm := Shuffle.commutative
  zero_mul := Shuffle.shuffle_zero_left
  mul_zero S := (Shuffle.commutative S _).trans (Shuffle.shuffle_zero_left S)
  left_distrib := Shuffle.shuffle_add_right
  right_distrib := Shuffle.shuffle_add_left

theorem smul_shuffle {X : Type} (a : ℝ) (S T : NCSeries X) :
    shuffle (a • S) T = a • shuffle S T := by
  funext w
  simp [shuffle, Pi.smul_apply, smul_eq_mul, ← List.sum_map_mul_left, mul_assoc]

instance {X : Type} : _root_.Algebra ℝ (Algebra X) :=
  _root_.Algebra.ofModule (fun a S T => smul_shuffle a S T) (by
    intro a S T
    change shuffle S (a • T) = a • shuffle S T
    rw [Shuffle.commutative S, Shuffle.commutative S]
    exact smul_shuffle a T S)

theorem list_prod {X : Type} (l : List (Algebra X)) :
    (l.prod : Algebra X) = shuffleList l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.prod_cons, ih]; rfl

theorem pow_eq {X : Type} (S : Algebra X) (n : ℕ) :
    (S ^ n : Algebra X) = shufflePow S n := by
  rw [← List.prod_replicate, list_prod]
  rfl

theorem monomial_eval {X : Type} {d : ℕ} (S : Fin d → Algebra X)
    (I : Fin d →₀ ℕ) (a : ℝ) :
    MvPolynomial.aeval S (MvPolynomial.monomial I a) =
      a • (shuffleMonomial S I : Algebra X) := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [← _root_.Algebra.smul_def]
  congr 1
  rw [← List.prod_ofFn, list_prod]
  simp only [pow_eq, shuffleMonomial]

theorem polynomial_eval {X : Type} {d : ℕ} (S : Fin d → Algebra X)
    (p : MvPolynomial (Fin d) ℝ) :
    (MvPolynomial.aeval S p : Algebra X) = SubstitutionFinite.polynomialSubstitution S p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, map_add]
  | monomial I a => rw [monomial_eval, SubstitutionFinite.polynomialSubstitution_monomial]

theorem polynomial_mul {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (p q : MvPolynomial (Fin d) ℝ) :
    SubstitutionFinite.polynomialSubstitution S (p * q) =
      shuffle (SubstitutionFinite.polynomialSubstitution S p)
        (SubstitutionFinite.polynomialSubstitution S q) := by
  let s : Fin d → Algebra X := fun i => S i
  calc
    SubstitutionFinite.polynomialSubstitution S (p * q) =
      (MvPolynomial.aeval s (p * q) : Algebra X) := (polynomial_eval s _).symm
    _ = shuffle (MvPolynomial.aeval s p) (MvPolynomial.aeval s q) :=
      (MvPolynomial.aeval s).map_mul p q
    _ = _ := congrArg₂ shuffle (polynomial_eval s p) (polynomial_eval s q)

end Lax825748Proofs.ShuffleAlgebra
