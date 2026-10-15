import Lax825748.ShuffleIdentities
import Lax825748Proofs.Series

noncomputable section

namespace Lax825748Proofs.Coproduct

open Lax825748.Series Lax825748.ShuffleIdentities
open Lax825748.LieRank
open scoped BigOperators

theorem sum_flatMap_map {α β M : Type*} [AddCommMonoid M]
    (l : List α) (k : α → List β) (f : β → M) :
    ((l.flatMap k).map f).sum = (l.map fun a => ((k a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem list_sum_fin_sum {α M : Type*} [AddCommMonoid M] {p : ℕ}
    (l : List α) (f : α → Fin p → M) :
    (l.map fun a => ∑ i, f a i).sum = ∑ i, (l.map fun a => f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

def slotWord {X : Type} {p : ℕ} (i : Fin p) (w : Word X) : Fin p → Word X :=
  fun j => if j = i then w else 1

def tensorLetter {X : Type} (p : ℕ) (x : X) : TensorPolynomial X p :=
  ∑ i : Fin p, MonoidAlgebra.single (slotWord i (FreeMonoid.of x)) 1

def wordCoproduct {X : Type} (p : ℕ) : Word X →* TensorPolynomial X p :=
  FreeMonoid.lift (tensorLetter p)

def coproductHom {X : Type} (p : ℕ) : NCPolynomial X →ₐ[ℝ] TensorPolynomial X p :=
  MonoidAlgebra.lift ℝ (TensorPolynomial X p) (Word X) (wordCoproduct p)

def distributedWord {X : Type} (p : ℕ) (w : Word X) : TensorPolynomial X p :=
  ((distributions p w.toList).map fun v =>
    MonoidAlgebra.single (fun i => FreeMonoid.ofList (v i)) 1).sum

theorem single_update {X : Type} {p : ℕ} (x : X) (v : Fin p → List X) (i : Fin p) :
    (MonoidAlgebra.single
      (fun j => FreeMonoid.ofList ((Function.update v i (x :: v i)) j))) (1 : ℝ) =
      MonoidAlgebra.single (slotWord i (FreeMonoid.of x)) 1 *
        MonoidAlgebra.single (fun j => FreeMonoid.ofList (v j)) 1 := by
  rw [MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp [slotWord]
  · simp [slotWord, h]

theorem distributed_cons {X : Type} (p : ℕ) (x : X) (w : Word X) :
    distributedWord p (FreeMonoid.of x * w) = tensorLetter p x * distributedWord p w := by
  simp only [distributedWord, FreeMonoid.toList_of_mul, distributions, sum_flatMap_map,
    List.map_ofFn, Function.comp_apply, List.sum_ofFn, single_update]
  rw [list_sum_fin_sum]
  simp only [List.sum_map_mul_left, tensorLetter, Finset.sum_mul]

theorem distributed_eq {X : Type} (p : ℕ) (w : Word X) :
    distributedWord p w = wordCoproduct p w := by
  induction w using FreeMonoid.recOn with
  | one =>
    simp [distributedWord, distributions, wordCoproduct, MonoidAlgebra.one_def]
    rfl
  | of_mul x w ih =>
    rw [distributed_cons, ih, map_mul]
    simp [wordCoproduct]

theorem coproduct_eq_hom {X : Type} (p : ℕ) (P : NCPolynomial X) :
    coproduct p P = coproductHom p P := by
  have hs (w : Word X) (a : ℝ) :
      ((distributions p w.toList).map fun v =>
        MonoidAlgebra.single (fun i => FreeMonoid.ofList (v i)) a).sum =
        a • distributedWord p w := by
    simp [distributedWord, List.smul_sum, List.map_map, Function.comp_def]
  simp only [coproduct, hs, distributed_eq]
  change P.coeff.sum (fun w a => a • wordCoproduct p w) = coproductHom p P
  calc
    _ = P.coeff.sum (fun w a => coproductHom p (MonoidAlgebra.single w a)) := by
      apply Finsupp.sum_congr
      intro w _
      simp [coproductHom]
    _ = coproductHom p (P.coeff.sum MonoidAlgebra.single) := (map_finsuppSum _ _ _).symm
    _ = _ := congrArg (coproductHom p) (MonoidAlgebra.sum_coeff_single P)

/--
---
conclusion: Lax825748.ShuffleIdentities.coproduct_multiplicative
---
-/
theorem coproduct_multiplicative {X : Type} (p : ℕ) (P Q : NCPolynomial X) :
    coproduct p (P * Q) = coproduct p P * coproduct p Q := by
  simp only [coproduct_eq_hom, map_mul]

def slotMonoid {X : Type} {p : ℕ} (i : Fin p) : Word X →* (Fin p → Word X) where
  toFun := slotWord i
  map_one' := by funext j; simp [slotWord]
  map_mul' u v := by funext j; by_cases h : j = i <;> simp [slotWord, h]

def slotHom {X : Type} {p : ℕ} (i : Fin p) :
    NCPolynomial X →ₐ[ℝ] TensorPolynomial X p :=
  MonoidAlgebra.lift ℝ (TensorPolynomial X p) (Word X)
    ((MonoidAlgebra.of ℝ _).comp (slotMonoid i))

@[simp] theorem slotHom_single {X : Type} {p : ℕ} (i : Fin p) (w : Word X) (a : ℝ) :
    slotHom i (MonoidAlgebra.single w a) = MonoidAlgebra.single (slotWord i w) a := by
  simp [slotHom, slotMonoid, MonoidAlgebra.of_apply]

theorem insertFactor_eq {X : Type} {p : ℕ} (i : Fin p) (P : NCPolynomial X) :
    insertFactor i P = slotHom i P := by
  change P.coeff.sum (fun w a => MonoidAlgebra.single (slotWord i w) a) = _
  calc
    _ = P.coeff.sum (fun w a => slotHom i (MonoidAlgebra.single w a)) := by simp only [slotHom_single]
    _ = slotHom i (P.coeff.sum MonoidAlgebra.single) := (map_finsuppSum _ _ _).symm
    _ = _ := congrArg (slotHom i) (MonoidAlgebra.sum_coeff_single P)

theorem slot_cross_commute {X : Type} {p : ℕ} (i j : Fin p) (h : i ≠ j)
    (P Q : NCPolynomial X) : slotHom i P * slotHom j Q = slotHom j Q * slotHom i P := by
  induction P using MonoidAlgebra.induction_on with
  | of u =>
    induction Q using MonoidAlgebra.induction_on with
    | of v =>
      change slotHom i (MonoidAlgebra.single u 1) * slotHom j (MonoidAlgebra.single v 1) =
        slotHom j (MonoidAlgebra.single v 1) * slotHom i (MonoidAlgebra.single u 1)
      simp only [slotHom_single, MonoidAlgebra.single_mul_single, one_mul]
      congr 1
      funext k
      by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [slotWord]
    | add P Q hP hQ => simp only [map_add, mul_add, add_mul, hP, hQ]
    | smul a P hP => simp only [map_smul, mul_smul_comm, smul_mul_assoc, hP]
  | add P Q hP hQ => simp only [map_add, add_mul, mul_add, hP, hQ]
  | smul a P hP => simp only [map_smul, smul_mul_assoc, mul_smul_comm, hP]

attribute [local instance] LieRing.ofAssociativeRing

theorem slot_lie_sum {X : Type} (p : ℕ) (P Q : NCPolynomial X) :
    ⁅(∑ i : Fin p, slotHom i P), (∑ i : Fin p, slotHom i Q)⁆ =
      ∑ i : Fin p, slotHom i ⁅P, Q⁆ := by
  simp only [sum_lie, lie_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul]
  · intro j _ hji
    rw [LieRing.of_associative_ring_bracket, slot_cross_commute i j (Ne.symm hji), sub_self]
  · simp

/--
---
conclusion: Lax825748.ShuffleIdentities.lie_primitive
---
-/
theorem lie_primitive {X : Type} (p : ℕ) (P : LiePolynomial X) :
    coproduct p P.val = ∑ i : Fin p, insertFactor i P.val := by
  simp only [coproduct_eq_hom, insertFactor_eq]
  apply LieSubalgebra.lieSpan_induction ℝ (x := P.val) (s := Set.range letter)
    (p := fun P _ => coproductHom p P = ∑ i : Fin p, slotHom i P)
    ?_ ?_ ?_ ?_ ?_ P.property
  · rintro _ ⟨x, rfl⟩
    simp [letter, wordPolynomial, coproductHom, wordCoproduct, tensorLetter]
  · simp
  · intro P Q _ _ hP hQ
    simp only [map_add, hP, hQ, Finset.sum_add_distrib]
  · intro a P _ hP
    simp only [map_smul, hP, Finset.smul_sum]
  · intro P Q _ _ hP hQ
    calc
      coproductHom p ⁅P, Q⁆ = ⁅coproductHom p P, coproductHom p Q⁆ := by
        simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul]
      _ = _ := by rw [hP, hQ, slot_lie_sum]

end Lax825748Proofs.Coproduct
