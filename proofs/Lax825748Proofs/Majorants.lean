import Lax825748Proofs.ConvergenceAlgebra

noncomputable section

namespace Lax825748Proofs.Majorants

open Lax208278.FormalSeries Lax208278.Monomials
open PowerSeriesBounds
open scoped BigOperators
open Finset.HasAntidiagonal

def Nonnegative {d : ℕ} (f : StateSeries d) : Prop :=
  ∀ I, 0 ≤ MvPowerSeries.coeff I f

def Bounds {d : ℕ} (f F : StateSeries d) : Prop :=
  ∀ I, |MvPowerSeries.coeff I f| ≤ MvPowerSeries.coeff I F

theorem Bounds.nonnegative {d : ℕ} {f F : StateSeries d} (h : Bounds f F) :
    Nonnegative F := fun I => (abs_nonneg _).trans (h I)

theorem Bounds.mono {d : ℕ} {f F G : StateSeries d} (h : Bounds f F)
    (hFG : ∀ I, MvPowerSeries.coeff I F ≤ MvPowerSeries.coeff I G) : Bounds f G :=
  fun I => (h I).trans (hFG I)

theorem bounds_self {d : ℕ} {F : StateSeries d} (hF : Nonnegative F) : Bounds F F :=
  fun I => (abs_of_nonneg (hF I)).le

theorem Bounds.trans {d : ℕ} {f F G : StateSeries d} (hf : Bounds f F)
    (hF : Bounds F G) : Bounds f G :=
  hf.mono fun I => (le_abs_self _).trans (hF I)

theorem Bounds.smul {d : ℕ} {f F : StateSeries d} (h : Bounds f F)
    {a : ℝ} (ha : 0 ≤ a) : Bounds (a • f) (a • F) := by
  intro I
  simpa only [MvPowerSeries.coeff_smul, abs_mul, abs_of_nonneg ha] using
    mul_le_mul_of_nonneg_left (h I) ha

theorem Bounds.mul {d : ℕ} {f g F G : StateSeries d} (hf : Bounds f F)
    (hg : Bounds g G) : Bounds (f * g) (F * G) := by
  intro I
  simp only [MvPowerSeries.coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro p _
  rw [abs_mul]
  exact mul_le_mul (hf _) (hg _) (abs_nonneg _) (hf.nonnegative _)

theorem Bounds.derivative {d : ℕ} {f F : StateSeries d} (h : Bounds f F) (i : Fin d) :
    Bounds (MvPowerSeries.pderiv ℝ i f) (MvPowerSeries.pderiv ℝ i F) := by
  intro I
  simp only [MvPowerSeries.coeff_pderiv, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ I i + 1)]
  exact mul_le_mul_of_nonneg_right (h _) (by positivity)

theorem nonnegative_one (d : ℕ) : Nonnegative (1 : StateSeries d) := by
  intro I
  classical
  simp only [MvPowerSeries.coeff_one]
  split_ifs <;> norm_num

theorem Nonnegative.pow {d : ℕ} {F : StateSeries d} (hF : Nonnegative F) (k : ℕ) :
    Nonnegative (F ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using nonnegative_one d
  | succ k ih =>
    rw [pow_succ]
    exact ((bounds_self ih).mul (bounds_self hF)).nonnegative

def geometric (d : ℕ) (C : ℝ) : StateSeries d := fun I => C ^ totalDegree I

@[simp] theorem coeff_geometric {d : ℕ} (C : ℝ) (I : Fin d →₀ ℕ) :
    MvPowerSeries.coeff I (geometric d C) = C ^ totalDegree I := rfl

theorem geometric_nonnegative (d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    Nonnegative (geometric d C) := fun _ => pow_nonneg hC _

theorem card_antidiagonal_lower {d : ℕ} (I : Fin d →₀ ℕ) (i : Fin d) :
    I i + 1 ≤ (antidiagonal I).card := by
  classical
  rw [← Finset.card_range (I i + 1)]
  apply Finset.card_le_card_of_injOn (fun k =>
    (Finsupp.single i k, I - Finsupp.single i k))
  · intro k hk
    change (Finsupp.single i k, I - Finsupp.single i k) ∈ antidiagonal I
    apply mem_antidiagonal.mpr
    apply Finsupp.ext
    intro j
    have hk' := Finset.mem_range.mp hk
    by_cases hj : i = j
    · subst j
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp [Finsupp.add_apply, Finsupp.tsub_apply, hj]
  · intro k _ l _ he
    have he' := congrArg (fun p : (Fin d →₀ ℕ) × (Fin d →₀ ℕ) => p.1 i) he
    simpa using he'

theorem geometric_derivative {d : ℕ} {C : ℝ} (hC : 0 ≤ C) (i : Fin d) :
    Bounds (MvPowerSeries.pderiv ℝ i (geometric d C))
      (C • (geometric d C ^ 2)) := by
  intro I
  have hdeg : totalDegree (I + Finsupp.single i 1 : Fin d →₀ ℕ) = totalDegree I + 1 :=
    (degree_add I (Finsupp.single i 1)).trans (by rw [degree_single])
  have hconv : MvPowerSeries.coeff I (geometric d C ^ 2) =
      (antidiagonal I).card * C ^ totalDegree I := by
    rw [pow_two, MvPowerSeries.coeff_mul]
    calc
      _ = ∑ _p ∈ antidiagonal I, C ^ totalDegree I := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [coeff_geometric]
        rw [← pow_add, ← degree_add, mem_antidiagonal.mp hp]
      _ = _ := by simp
  rw [MvPowerSeries.coeff_pderiv, coeff_geometric, hdeg,
    abs_mul, abs_of_nonneg (pow_nonneg hC _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ I i + 1),
    MvPowerSeries.coeff_smul, hconv, pow_succ]
  have hc : (I i : ℝ) + 1 ≤ (antidiagonal I).card := by exact_mod_cast card_antidiagonal_lower I i
  calc
    _ = (C * C ^ totalDegree I) * ((I i : ℝ) + 1) := by ring
    _ ≤ (C * C ^ totalDegree I) * (antidiagonal I).card :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

theorem geometric_pow_derivative {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (i : Fin d) (k : ℕ) :
    Bounds (MvPowerSeries.pderiv ℝ i (geometric d C ^ (k + 1)))
      ((((k + 1 : ℕ) : ℝ) * C) • (geometric d C ^ (k + 2))) := by
  let F := geometric d C
  have hm := ((bounds_self ((geometric_nonnegative d hC).pow k)).mul
    (geometric_derivative hC i)).smul (show (0 : ℝ) ≤ k + 1 by positivity)
  have hl : MvPowerSeries.pderiv ℝ i (F ^ (k + 1)) =
      ((k : ℝ) + 1) • (F ^ k * MvPowerSeries.pderiv ℝ i F) := by
    rw [MvPowerSeries.pderiv_pow]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp [Algebra.smul_def, mul_assoc]
  rw [hl]
  convert hm using 1
  simp only [mul_smul_comm, smul_smul, ← pow_add, Nat.cast_add, Nat.cast_one]

end Lax825748Proofs.Majorants
