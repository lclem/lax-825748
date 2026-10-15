import Lax825748.ShuffleIdentities
import Lax825748Proofs.Series
import Mathlib.Tactic

noncomputable section

namespace Lax825748Proofs.Shuffle

open Lax825748.Series Lax825748.Shuffle

def shift {X : Type} (x : X) (S : NCSeries X) : NCSeries X :=
  fun w => S (FreeMonoid.of x * w)

@[simp] theorem shuffle_empty {X : Type} (S T : NCSeries X) :
    shuffle S T 1 = S 1 * T 1 := by
  simp [shuffle, unshuffles]

theorem shuffle_cons {X : Type} (x : X) (w : Word X) (S T : NCSeries X) :
    shuffle S T (FreeMonoid.of x * w) =
      shuffle (shift x S) T w + shuffle S (shift x T) w := by
  change (((unshuffles w.toList).flatMap fun p =>
    [(x :: p.1, p.2), (p.1, x :: p.2)]).map fun p =>
    S (FreeMonoid.ofList p.1) * T (FreeMonoid.ofList p.2)).sum = _
  simp only [shuffle, shift]
  generalize unshuffles w.toList = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [ih]
    simp only [FreeMonoid.ofList_cons]
    ring

/--
---
conclusion: Lax825748.Shuffle.commutative
---
-/
theorem commutative {X : Type} (S T : NCSeries X) : shuffle S T = shuffle T S := by
  funext w
  induction w using FreeMonoid.recOn generalizing S T with
  | one => simpa only [shuffle_empty] using mul_comm (S 1) (T 1)
  | of_mul x w ih =>
    rw [shuffle_cons, shuffle_cons, ih (shift x S) T, ih S (shift x T), add_comm]

theorem shift_shuffle {X : Type} (x : X) (S T : NCSeries X) :
    shift x (shuffle S T) = shuffle (shift x S) T + shuffle S (shift x T) := by
  funext w
  exact shuffle_cons x w S T

theorem shuffle_add_left {X : Type} (R S T : NCSeries X) :
    shuffle (R + S) T = shuffle R T + shuffle S T := by
  funext w
  simp [shuffle, add_mul, List.sum_map_add]

theorem shuffle_add_right {X : Type} (R S T : NCSeries X) :
    shuffle R (S + T) = shuffle R S + shuffle R T := by
  rw [commutative, shuffle_add_left, commutative S R, commutative T R]

/--
---
conclusion: Lax825748.Shuffle.associative
---
-/
theorem associative {X : Type} (R S T : NCSeries X) :
    shuffle (shuffle R S) T = shuffle R (shuffle S T) := by
  funext w
  induction w using FreeMonoid.recOn generalizing R S T with
  | one => simpa only [shuffle_empty] using mul_assoc (R 1) (S 1) (T 1)
  | of_mul x w ih =>
    simp only [shuffle_cons, shift_shuffle, shuffle_add_left, shuffle_add_right, Pi.add_apply]
    rw [ih, ih, ih]
    exact add_assoc _ _ _

@[simp] theorem shuffle_zero_left {X : Type} (S : NCSeries X) : shuffle 0 S = 0 := by
  funext w
  simp [shuffle]

@[simp] theorem shift_constant {X : Type} (x : X) (a : ℝ) :
    shift x (constantSeries a) = 0 := by
  funext w
  have h : FreeMonoid.of x * w ≠ 1 := by
    intro he
    have := congrArg FreeMonoid.toList he
    simp at this
  simp [shift, constantSeries, h]

/--
---
conclusion: Lax825748.Shuffle.unit
---
-/
theorem unit {X : Type} (S : NCSeries X) : shuffle (constantSeries 1) S = S := by
  funext w
  induction w using FreeMonoid.recOn generalizing S with
  | one => simp [shuffle_empty, constantSeries]
  | of_mul x w ih =>
    rw [shuffle_cons, shift_constant, shuffle_zero_left, Pi.zero_apply, zero_add, ih]
    rfl

theorem residual_letter_eq_shift {X : Type} (x : X) (S : NCSeries X) :
    rightResidual S (letter x) = shift x S := by
  funext w
  exact Series.right_residual_word S (FreeMonoid.of x) w

/--
---
conclusion: Lax825748.ShuffleIdentities.residual_derivation
---
-/
theorem residual_derivation {X : Type} (x : X) (S T : NCSeries X) :
    rightResidual (shuffle S T) (letter x) =
      shuffle (rightResidual S (letter x)) T + shuffle S (rightResidual T (letter x)) := by
  simp only [residual_letter_eq_shift]
  exact shift_shuffle x S T

end Lax825748Proofs.Shuffle
