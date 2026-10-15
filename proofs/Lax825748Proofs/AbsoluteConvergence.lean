import Lax825748Proofs.PowerSeriesBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section

namespace Lax825748Proofs.AbsoluteConvergence

open Lax825748.FormalSeries Lax825748.Monomials Lax825748.ConvergentSeries
open scoped BigOperators

def splitIndex (d : ℕ) : (Fin (d + 1) → ℕ) ≃ ℕ × (Fin d → ℕ) where
  toFun I := (I 0, fun i => I i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv I := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := rfl

theorem geometric_functions (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun I : Fin d → ℕ => r ^ totalDegree I) := by
  induction d with
  | zero =>
    let : Fintype (Fin 0 → ℕ) := Fintype.ofFinite _
    exact (hasSum_fintype _).summable
  | succ d ih =>
    have hs := (summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)).mul_of_nonneg
      ih (fun _ => pow_nonneg hr _) (fun _ => pow_nonneg hr _)
    have he := (splitIndex d).summable_iff.mpr hs
    change Summable (fun I : Fin (d + 1) → ℕ =>
      r ^ I 0 * r ^ totalDegree (fun i => I i.succ)) at he
    simpa only [totalDegree, Fin.sum_univ_succ, pow_add] using he

theorem geometric_indices (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun I : Fin d →₀ ℕ => r ^ totalDegree I) := by
  exact (geometric_functions d hr hr1).comp_injective
    (i := fun I : Fin d →₀ ℕ => (I : Fin d → ℕ))
    (fun I J he => Finsupp.ext fun i => congrFun he i)

/--
---
conclusion: Lax825748.AnalyticCalculus.absolute_convergence
---
A geometric coefficient bound is summable after reducing the polyradius.
Conversely, the sum of absolute terms bounds each weighted coefficient.
-/
theorem absolute_convergence {d : ℕ} (f : StateSeries d) :
    Convergent f ↔ ∃ r : ℝ, 0 < r ∧
      Summable (fun I : Fin d →₀ ℕ => |MvPowerSeries.coeff I f| * r ^ totalDegree I) := by
  constructor
  · rintro ⟨α, hα, C, hC, hb⟩
    let r := (2 * C)⁻¹
    have hr : 0 < r := by dsimp [r]; positivity
    have hCr : C * r = 1 / 2 := by dsimp [r]; field_simp
    refine ⟨r, hr, ?_⟩
    have hs : Summable (fun I : Fin d →₀ ℕ => α * (C * r) ^ totalDegree I) := by
      rw [hCr]
      exact (geometric_indices d (by norm_num) (by norm_num)).mul_left α
    apply Summable.of_nonneg_of_le (fun I => mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _)) _ hs
    intro I
    calc
      _ ≤ (α * C ^ totalDegree I) * r ^ totalDegree I :=
        mul_le_mul_of_nonneg_right (hb I) (pow_nonneg hr.le _)
      _ = _ := by rw [mul_pow]; ring
  · rintro ⟨r, hr, hs⟩
    let M := ∑' I : Fin d →₀ ℕ, |MvPowerSeries.coeff I f| * r ^ totalDegree I
    have hM : 0 ≤ M := tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _)
    refine ⟨M + 1, by positivity, r⁻¹, inv_pos.mpr hr, ?_⟩
    intro I
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hr _)).mpr
    exact (hs.le_tsum I (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _))).trans
      (by dsimp [M]; linarith)

end Lax825748Proofs.AbsoluteConvergence
