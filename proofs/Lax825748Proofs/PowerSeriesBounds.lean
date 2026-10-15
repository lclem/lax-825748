import Lax825748.AnalyticCalculus
import Mathlib.Tactic

noncomputable section

namespace Lax825748Proofs.PowerSeriesBounds

open Lax825748.FormalSeries Lax825748.Monomials Lax825748.ConvergentSeries
open scoped BigOperators

theorem degree_add {d : ℕ} (I J : Fin d →₀ ℕ) :
    totalDegree (I + J : Fin d →₀ ℕ) = totalDegree I + totalDegree J := by
  simp [totalDegree, Finset.sum_add_distrib]

theorem degree_single {d : ℕ} (i : Fin d) (n : ℕ) :
    totalDegree (Finsupp.single i n : Fin d →₀ ℕ) = n := by
  simp [totalDegree, Finsupp.single_apply]

theorem bound_mono {d : ℕ} {f : StateSeries d} {α β C D : ℝ}
    (hf : HasGeometricBound f α C) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (ha : α ≤ β) (hc : C ≤ D) : HasGeometricBound f β D := by
  intro I
  refine (hf I).trans ?_
  have hβ : 0 ≤ β := hα.trans ha
  gcongr

theorem convergent_C {d : ℕ} (a : ℝ) : Convergent (MvPowerSeries.C a : StateSeries d) := by
  refine ⟨|a| + 1, by positivity, 1, by norm_num, ?_⟩
  intro I
  by_cases hI : I = 0
  · subst I
    simp
  · simp only [MvPowerSeries.coeff_C, if_neg hI, abs_zero, one_pow, mul_one]
    positivity

theorem convergent_X {d : ℕ} (i : Fin d) : Convergent (MvPowerSeries.X i : StateSeries d) := by
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro I
  simp only [MvPowerSeries.coeff_X, one_pow, one_mul]
  split_ifs <;> norm_num

theorem convergent_add {d : ℕ} {f g : StateSeries d}
    (hf : Convergent f) (hg : Convergent g) : Convergent (f + g) := by
  obtain ⟨α, hα, C, hC, hb⟩ := hf
  obtain ⟨β, hβ, D, hD, hd⟩ := hg
  refine ⟨α + β, add_pos hα hβ, max C D, lt_max_iff.mpr (.inl hC), ?_⟩
  intro I
  rw [map_add]
  calc
    _ ≤ |MvPowerSeries.coeff I f| + |MvPowerSeries.coeff I g| := abs_add_le _ _
    _ ≤ α * max C D ^ totalDegree I + β * max C D ^ totalDegree I :=
      add_le_add (bound_mono hb hα.le hC.le le_rfl (le_max_left _ _) I)
        (bound_mono hd hβ.le hD.le le_rfl (le_max_right _ _) I)
    _ = _ := by ring

theorem convergent_smul {d : ℕ} (a : ℝ) {f : StateSeries d}
    (hf : Convergent f) : Convergent (a • f) := by
  obtain ⟨α, hα, C, hC, hb⟩ := hf
  refine ⟨(|a| + 1) * α, by positivity, C, hC, ?_⟩
  intro I
  simp only [map_smul, smul_eq_mul, abs_mul]
  calc
    _ ≤ (|a| + 1) * (α * C ^ totalDegree I) := by
      gcongr
      · linarith
      · exact hb I
    _ = _ := by ring

theorem common_bounds {ι : Type} [Fintype ι] {d : ℕ}
    (f : ι → StateSeries d) (hf : ∀ i, Convergent (f i)) :
    ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∀ i, HasGeometricBound (f i) α C := by
  classical
  choose α hα C hC hb using hf
  have hαsum : 0 ≤ ∑ i, α i := Finset.sum_nonneg fun i _ => (hα i).le
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨1 + ∑ i, α i, by positivity, 1 + ∑ i, C i, by positivity, ?_⟩
  intro i
  apply bound_mono (hb i) (hα i).le (hC i).le
  · have := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hα j).le) (Finset.mem_univ i)
    linarith
  · have := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hC j).le) (Finset.mem_univ i)
    linarith

/--
---
conclusion: Lax825748.AnalyticCalculus.partial_derivative
---
Differentiation multiplies a coefficient by at most $|I|+1\leq 2^{|I|}$;
enlarging the geometric constant preserves convergence.
-/
theorem partial_derivative {d : ℕ} (f : StateSeries d) (hf : Convergent f)
    (i : Fin d) : Convergent (MvPowerSeries.pderiv ℝ i f) := by
  obtain ⟨α, hα, C, hC, hb⟩ := hf
  refine ⟨α * C, mul_pos hα hC, 2 * C, by positivity, ?_⟩
  intro I
  have hi : I i ≤ totalDegree I :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hip : (I i : ℝ) + 1 ≤ (2 : ℝ) ^ totalDegree I := by
    exact_mod_cast (Nat.succ_le_of_lt (hi.trans_lt Nat.lt_two_pow_self))
  have hdeg : totalDegree (I + Finsupp.single i 1 : Fin d →₀ ℕ) =
      totalDegree I + 1 := by
    change (∑ j, (I + Finsupp.single i 1 : Fin d →₀ ℕ) j) = _
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]
    simp [totalDegree]
  rw [MvPowerSeries.coeff_pderiv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < I i + 1)]
  calc
    _ ≤ (α * C ^ (totalDegree I + 1)) * (2 : ℝ) ^ totalDegree I := by
      apply mul_le_mul _ hip (by positivity) (by positivity)
      exact (hb (I + Finsupp.single i 1)).trans_eq (congrArg (fun n => α * C ^ n) hdeg)
    _ = _ := by rw [pow_succ, mul_pow]; ring

end Lax825748Proofs.PowerSeriesBounds
