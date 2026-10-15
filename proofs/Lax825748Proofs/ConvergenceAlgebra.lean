import Lax825748Proofs.PowerSeriesBounds
import Mathlib.Data.Finsupp.Interval

noncomputable section

namespace Lax825748Proofs.ConvergenceAlgebra

open Lax825748.FormalSeries Lax825748.Monomials Lax825748.ConvergentSeries
open PowerSeriesBounds
open scoped BigOperators
open Finset.HasAntidiagonal

theorem antidiagonal_card {d : ℕ} (I : Fin d →₀ ℕ) :
    (antidiagonal I).card ≤ 2 ^ totalDegree I := by
  classical
  have hc : (antidiagonal I).card ≤ (Finset.Iic I).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      change p.1 ∈ Finset.Iic I
      rw [Finset.mem_Iic]
      have he := mem_antidiagonal.mp hp
      rw [← he]
      exact le_add_of_nonneg_right zero_le
    · intro p hp q hq he
      apply Prod.ext he
      have hp' := mem_antidiagonal.mp hp
      have hq' := mem_antidiagonal.mp hq
      rw [he] at hp'
      exact add_left_cancel (hp'.trans hq'.symm)
  apply hc.trans
  rw [Finsupp.card_Iic]
  calc
    _ = ∏ i ∈ I.support, (I i + 1) := by simp
    _ ≤ ∏ i ∈ I.support, 2 ^ I i :=
      Finset.prod_le_prod' fun i _ => Nat.succ_le_of_lt Nat.lt_two_pow_self
    _ = 2 ^ totalDegree I := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      exact Finsupp.sum_fintype I (fun _ n => n) (fun _ => rfl)

theorem product_bound {d : ℕ} (f g : StateSeries d) {α β C : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hf : HasGeometricBound f α C) (hg : HasGeometricBound g β C) :
    HasGeometricBound (f * g) (α * β) (2 * C) := by
  intro I
  rw [MvPowerSeries.coeff_mul]
  calc
    _ ≤ ∑ p ∈ antidiagonal I, |MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ antidiagonal I, (α * β) * C ^ totalDegree I := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      calc
        _ ≤ (α * C ^ totalDegree p.1) * (β * C ^ totalDegree p.2) := by
          apply mul_le_mul (hf _) (hg _) (abs_nonneg _) (by positivity)
        _ = (α * β) * C ^ totalDegree I := by
          rw [← mem_antidiagonal.mp hp]
          rw [degree_add, pow_add]
          ring
    _ = (antidiagonal I).card * ((α * β) * C ^ totalDegree I) := by simp
    _ ≤ (2 : ℝ) ^ totalDegree I * ((α * β) * C ^ totalDegree I) := by
      gcongr
      exact_mod_cast antidiagonal_card I
    _ = _ := by rw [mul_pow]; ring

theorem convergent_mul {d : ℕ} {f g : StateSeries d}
    (hf : Convergent f) (hg : Convergent g) : Convergent (f * g) := by
  obtain ⟨α, hα, C, hC, hb⟩ := hf
  obtain ⟨β, hβ, D, hD, hd⟩ := hg
  refine ⟨α * β, mul_pos hα hβ, 2 * max C D, by positivity, ?_⟩
  exact product_bound f g hα.le hβ.le (hC.le.trans (le_max_left _ _))
    (bound_mono hb hα.le hC.le le_rfl (le_max_left _ _))
    (bound_mono hd hβ.le hD.le le_rfl (le_max_right _ _))

/--
---
conclusion: Lax825748.AnalyticCalculus.subalgebra
---
Coefficient convolution preserves geometric bounds after enlarging the
geometric constant. Addition and constants obey the same condition.
-/
theorem subalgebra (d : ℕ) :
    ∃ A : Subalgebra ℝ (StateSeries d), ∀ f, f ∈ A ↔ Convergent f := by
  let A : Subalgebra ℝ (StateSeries d) :=
    { carrier := {f | Convergent f}
      algebraMap_mem' := fun a => convergent_C a
      zero_mem' := by simpa using (convergent_C (d := d) 0)
      one_mem' := by simpa using (convergent_C (d := d) 1)
      add_mem' := fun hf hg => convergent_add hf hg
      mul_mem' := fun hf hg => convergent_mul hf hg }
  exact ⟨A, fun _ => Iff.rfl⟩

end Lax825748Proofs.ConvergenceAlgebra
