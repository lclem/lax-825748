import Lax825748.RepresentationMap
import Lax825748Proofs.Shuffle

noncomputable section

namespace Lax825748Proofs.RepresentationMap

open Lax825748.Series Lax825748.FormalSeries Lax825748.DifferentialRepresentation
open Lax825748.RepresentationMap Lax825748.Shuffle
open scoped BigOperators

@[simp] theorem field_zero {d : ℕ} (A : VectorField d) : applyVectorField A 0 = 0 := by
  simp [applyVectorField]

@[simp] theorem field_C {d : ℕ} (A : VectorField d) (a : ℝ) :
    applyVectorField A (MvPowerSeries.C a) = 0 := by
  simp [applyVectorField]

theorem field_add {d : ℕ} (A : VectorField d) (f g : StateSeries d) :
    applyVectorField A (f + g) = applyVectorField A f + applyVectorField A g := by
  simp [applyVectorField, mul_add, Finset.sum_add_distrib]

theorem field_smul {d : ℕ} (A : VectorField d) (a : ℝ) (f : StateSeries d) :
    applyVectorField A (a • f) = a • applyVectorField A f := by
  simp [applyVectorField, Finset.smul_sum]

theorem field_mul {d : ℕ} (A : VectorField d) (f g : StateSeries d) :
    applyVectorField A (f * g) = applyVectorField A f * g + f * applyVectorField A g := by
  simp only [applyVectorField, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [(MvPowerSeries.pderiv ℝ i).leibniz]
  simp only [smul_eq_mul]
  ring

@[simp] theorem act_one {X : Type} {d : ℕ} (R : Representation X d) (f : StateSeries d) :
    act R f 1 = f := rfl

theorem act_cons {X : Type} {d : ℕ} (R : Representation X d) (f : StateSeries d)
    (x : X) (w : Word X) :
    act R f (FreeMonoid.of x * w) = act R (applyVectorField (R.fields x) f) w := rfl

theorem act_mul {X : Type} {d : ℕ} (R : Representation X d) (f : StateSeries d)
    (u v : Word X) : act R f (u * v) = act R (act R f u) v := by
  exact List.foldl_append

@[simp] theorem act_zero {X : Type} {d : ℕ} (R : Representation X d) (w : Word X) :
    act R 0 w = 0 := by
  induction w using FreeMonoid.recOn with
  | one => rfl
  | of_mul x w ih => simpa [act_cons] using ih

theorem act_add {X : Type} {d : ℕ} (R : Representation X d) (w : Word X)
    (f g : StateSeries d) : act R (f + g) w = act R f w + act R g w := by
  induction w using FreeMonoid.recOn generalizing f g with
  | one => rfl
  | of_mul x w ih => simp only [act_cons, field_add, ih]

theorem act_smul {X : Type} {d : ℕ} (R : Representation X d) (w : Word X)
    (a : ℝ) (f : StateSeries d) : act R (a • f) w = a • act R f w := by
  induction w using FreeMonoid.recOn generalizing f with
  | one => rfl
  | of_mul x w ih => simp only [act_cons, field_smul, ih]

@[simp] theorem eta_zero {X : Type} {d : ℕ} (R : Representation X d) : eta R 0 = 0 := by
  funext w
  simp [eta]

theorem eta_add {X : Type} {d : ℕ} (R : Representation X d) (f g : StateSeries d) :
    eta R (f + g) = eta R f + eta R g := by
  funext w
  simp [eta, act_add]

theorem eta_shift {X : Type} {d : ℕ} (R : Representation X d) (x : X)
    (f : StateSeries d) :
    eta R (applyVectorField (R.fields x) f) = Shuffle.shift x (eta R f) := rfl

/--
---
conclusion: Lax825748.RepresentationMap.intertwining
---
-/
theorem intertwining {X : Type} {d : ℕ} (R : Representation X d)
    (k : StateSeries d) (w : Word X) :
    eta R (act R k w) = rightResidual (eta R k) (wordPolynomial w) := by
  funext v
  rw [Series.right_residual_word]
  exact congrArg MvPowerSeries.constantCoeff (act_mul R k w v).symm

/--
---
conclusion: Lax825748.RepresentationMap.algebra_homomorphism
---
-/
theorem algebra_homomorphism {X : Type} {d : ℕ} (R : Representation X d) :
    (∀ a : ℝ, eta R (MvPowerSeries.C a) = constantSeries a) ∧
    (∀ f k, eta R (f + k) = eta R f + eta R k) ∧
    (∀ f k, eta R (f * k) = shuffle (eta R f) (eta R k)) := by
  refine ⟨?_, eta_add R, ?_⟩
  · intro a
    funext w
    induction w using FreeMonoid.recOn with
    | one => simp [eta, constantSeries]
    | of_mul x w ih =>
      change Shuffle.shift x (eta R (MvPowerSeries.C a)) w =
        Shuffle.shift x (constantSeries a) w
      rw [← eta_shift, field_C, eta_zero, Shuffle.shift_constant]
  · intro f g
    funext w
    induction w using FreeMonoid.recOn generalizing f g with
    | one => simp [eta]
    | of_mul x w ih =>
      change Shuffle.shift x (eta R (f * g)) w = _
      rw [← eta_shift, field_mul, eta_add]
      simp only [Pi.add_apply, ih, Shuffle.shuffle_cons, ← eta_shift]

open Lax825748.Monomials

theorem degree_add {d : ℕ} (I J : Fin d →₀ ℕ) :
    totalDegree (I + J) = totalDegree I + totalDegree J := by
  simp [totalDegree, Finset.sum_add_distrib]

theorem degree_single {d : ℕ} (i : Fin d) : totalDegree (Finsupp.single i 1) = 1 := by
  simp [totalDegree, Finsupp.single_apply]

theorem agree_mul_left {d N : ℕ} (A f g : StateSeries d)
    (h : Lax825748.FormalSeries.AgreeBelow N f g) :
    Lax825748.FormalSeries.AgreeBelow N (A * f) (A * g) := by
  intro I hI
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = I := Finset.mem_antidiagonal.mp hij
  have hd := degree_add ij.1 ij.2
  rw [he] at hd
  rw [h ij.2 (by omega)]

theorem agree_derivative {d N : ℕ} (i : Fin d) (f g : StateSeries d)
    (h : Lax825748.FormalSeries.AgreeBelow (N + 1) f g) :
    Lax825748.FormalSeries.AgreeBelow N
      (MvPowerSeries.pderiv ℝ i f) (MvPowerSeries.pderiv ℝ i g) := by
  intro I hI
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    h (I + Finsupp.single i 1) (by rw [degree_add, degree_single]; omega)]

theorem agree_field {d N : ℕ} (A : VectorField d) (f g : StateSeries d)
    (h : Lax825748.FormalSeries.AgreeBelow (N + 1) f g) :
    Lax825748.FormalSeries.AgreeBelow N (applyVectorField A f) (applyVectorField A g) := by
  intro I hI
  simp only [applyVectorField, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact agree_mul_left (A i) _ _ (agree_derivative i f g h) I hI

theorem agree_act {X : Type} {d N : ℕ} (R : Representation X d) (w : Word X)
    (f g : StateSeries d) (h : Lax825748.FormalSeries.AgreeBelow (N + w.toList.length) f g) :
    Lax825748.FormalSeries.AgreeBelow N (act R f w) (act R g w) := by
  induction w using FreeMonoid.recOn generalizing f g with
  | one => simpa using h
  | of_mul x w ih =>
    simp only [act_cons]
    apply ih
    apply agree_field
    convert h using 1
    simp [Nat.add_comm, Nat.add_left_comm]

/--
---
conclusion: Lax825748.RepresentationMap.continuous
---
-/
theorem continuous {X : Type} {d : ℕ} (R : Representation X d) :
    ∀ N, ∃ M, ∀ f k, Lax825748.FormalSeries.AgreeBelow M f k →
      Lax825748.Series.AgreeBelow N (eta R f) (eta R k) := by
  intro N
  refine ⟨N, ?_⟩
  intro f k h w hw
  have ha : Lax825748.FormalSeries.AgreeBelow (1 + w.toList.length) f k :=
    fun I hI => h I (by omega)
  have := agree_act (N := 1) R w f k ha 0 (by simp [totalDegree])
  simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, eta] using this

end Lax825748Proofs.RepresentationMap
