import Lax825748Proofs.AbsoluteConvergence
import Lax825748Proofs.ConvergenceAlgebra

noncomputable section

namespace Lax825748Proofs.WeightedMass

open Lax208278.FormalSeries Lax208278.Monomials Lax825748.ConvergentSeries
open PowerSeriesBounds
open scoped BigOperators
open Finset.HasAntidiagonal

def weight {d : ℕ} (f : StateSeries d) (r : ℝ) (I : Fin d →₀ ℕ) : ℝ :=
  |MvPowerSeries.coeff I f| * r ^ totalDegree I

def AtRadius {d : ℕ} (f : StateSeries d) (r : ℝ) : Prop := Summable (weight f r)

def mass {d : ℕ} (f : StateSeries d) (r : ℝ) : ℝ := ∑' I, weight f r I

theorem weight_nonnegative {d : ℕ} (f : StateSeries d) {r : ℝ} (hr : 0 ≤ r)
    (I : Fin d →₀ ℕ) : 0 ≤ weight f r I := by unfold weight; positivity

theorem mass_nonnegative {d : ℕ} (f : StateSeries d) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ mass f r := tsum_nonneg (weight_nonnegative f hr)

theorem weight_le_mass {d : ℕ} {f : StateSeries d} {r : ℝ} (hr : 0 ≤ r)
    (hf : AtRadius f r) (I : Fin d →₀ ℕ) : weight f r I ≤ mass f r :=
  hf.le_tsum I (fun _ _ => weight_nonnegative f hr _)

theorem weight_mul_le {d : ℕ} (f g : StateSeries d) {r : ℝ} (hr : 0 ≤ r)
    (I : Fin d →₀ ℕ) :
    weight (f * g) r I ≤ ∑ p ∈ antidiagonal I, weight f r p.1 * weight g r p.2 := by
  unfold weight
  rw [MvPowerSeries.coeff_mul]
  calc
    _ ≤ (∑ p ∈ antidiagonal I,
        |MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g|) * r ^ totalDegree I :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hr _)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← mem_antidiagonal.mp hp, degree_add, pow_add, abs_mul]
      ring

theorem AtRadius.mul {d : ℕ} {f g : StateSeries d} {r : ℝ} (hf : AtRadius f r)
    (hg : AtRadius g r) (hr : 0 ≤ r) : AtRadius (f * g) r := by
  have hs := hf.mul_of_nonneg hg (weight_nonnegative f hr) (weight_nonnegative g hr)
  exact Summable.of_nonneg_of_le (weight_nonnegative _ hr) (weight_mul_le f g hr)
    (summable_sum_mul_antidiagonal_of_summable_mul hs)

theorem mass_mul_le {d : ℕ} {f g : StateSeries d} {r : ℝ} (hf : AtRadius f r)
    (hg : AtRadius g r) (hr : 0 ≤ r) : mass (f * g) r ≤ mass f r * mass g r := by
  have hs := hf.mul_of_nonneg hg (weight_nonnegative f hr) (weight_nonnegative g hr)
  simp only [mass]
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hs]
  exact (hf.mul hg hr).tsum_le_tsum (weight_mul_le f g hr)
    (summable_sum_mul_antidiagonal_of_summable_mul hs)

theorem weight_one {d : ℕ} (r : ℝ) (I : Fin d →₀ ℕ) :
    weight (1 : StateSeries d) r I = if I = 0 then 1 else 0 := by
  classical
  by_cases hi : I = 0
  · subst I
    simp [weight, totalDegree]
  · simp [weight, MvPowerSeries.coeff_one, hi]

theorem radius_one (d : ℕ) (r : ℝ) : AtRadius (1 : StateSeries d) r := by
  change Summable (fun I => weight (1 : StateSeries d) r I)
  simp_rw [weight_one]
  exact (hasSum_single (0 : Fin d →₀ ℕ) (fun I hI => by simp [hI])).summable

@[simp] theorem mass_one (d : ℕ) (r : ℝ) : mass (1 : StateSeries d) r = 1 := by
  unfold mass
  simp_rw [weight_one]
  simp

theorem AtRadius.pow {d : ℕ} {f : StateSeries d} {r : ℝ} (hf : AtRadius f r)
    (hr : 0 ≤ r) (k : ℕ) : AtRadius (f ^ k) r := by
  induction k with
  | zero => simpa using radius_one d r
  | succ k ih => simpa only [pow_succ] using ih.mul hf hr

theorem mass_pow_le {d : ℕ} {f : StateSeries d} {r : ℝ} (hf : AtRadius f r)
    (hr : 0 ≤ r) (k : ℕ) : mass (f ^ k) r ≤ mass f r ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (mass_mul_le (hf.pow hr k) hf hr).trans
      (mul_le_mul_of_nonneg_right ih (mass_nonnegative f hr))

theorem AtRadius.prod {ι : Type} {d : ℕ} (s : Finset ι) (f : ι → StateSeries d)
    {r : ℝ} (hf : ∀ i ∈ s, AtRadius (f i) r) (hr : 0 ≤ r) :
    AtRadius (∏ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radius_one d r
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi]))) hr

theorem mass_prod_le {ι : Type} {d : ℕ} (s : Finset ι) (f : ι → StateSeries d)
    {r : ℝ} (hf : ∀ i ∈ s, AtRadius (f i) r) (hr : 0 ≤ r) :
    mass (∏ i ∈ s, f i) r ≤ ∏ i ∈ s, mass (f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (mass_mul_le (hf a (by simp)) (AtRadius.prod s f hs hr) hr).trans
      (mul_le_mul_of_nonneg_left (ih hs) (mass_nonnegative _ hr))

theorem AtRadius.shrink {d : ℕ} {f : StateSeries d} {r s : ℝ} (hf : AtRadius f r)
    (hs : 0 ≤ s) (hsr : s ≤ r) : AtRadius f s :=
  Summable.of_nonneg_of_le (weight_nonnegative f hs)
    (fun _I => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hsr _) (abs_nonneg _)) hf

theorem weight_scale {d : ℕ} (f : StateSeries d) (r t : ℝ) (I : Fin d →₀ ℕ) :
    weight f (t * r) I = t ^ totalDegree I * weight f r I := by
  simp only [weight, mul_pow]
  ring

theorem mass_scale_zero {d : ℕ} {f : StateSeries d} {r t : ℝ} (hf : AtRadius f r)
    (h0 : MvPowerSeries.constantCoeff f = 0) (hr : 0 ≤ r) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    mass f (t * r) ≤ t * mass f r := by
  have hsmall : t * r ≤ r := by nlinarith
  have hm : ∀ I, weight f (t * r) I ≤ t * weight f r I := by
    intro I
    by_cases hi : I = 0
    · subst I
      simp [weight, MvPowerSeries.coeff_zero_eq_constantCoeff, h0]
    · have hn : 0 < totalDegree I := by
        by_contra! hh
        have hz : ∀ i, I i = 0 := fun i => by
          have hle : I i ≤ totalDegree I := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        exact hi (Finsupp.ext hz)
      rw [weight_scale]
      apply mul_le_mul_of_nonneg_right _ (weight_nonnegative f hr I)
      obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      rw [he, pow_succ]
      exact mul_le_of_le_one_left ht (pow_le_one₀ ht ht1)
  have hs := (hf.shrink (mul_nonneg ht hr) hsmall).tsum_le_tsum hm (hf.mul_left t)
  simpa only [mass, tsum_mul_left] using hs

theorem bound_radius {d : ℕ} {f : StateSeries d} {α C r : ℝ}
    (hf : HasGeometricBound f α C) (_hα : 0 ≤ α) (hr : 0 ≤ r)
    (hCr : 0 ≤ C * r) (hCr1 : C * r < 1) : AtRadius f r := by
  have hs := (AbsoluteConvergence.geometric_indices d hCr hCr1).mul_left α
  apply Summable.of_nonneg_of_le (weight_nonnegative f hr) _ hs
  intro I
  calc
    _ ≤ (α * C ^ totalDegree I) * r ^ totalDegree I :=
      mul_le_mul_of_nonneg_right (hf I) (pow_nonneg hr _)
    _ = _ := by rw [mul_pow]; ring

theorem common_small_radius {ι : Type} [Fintype ι] {d : ℕ}
    (f : ι → StateSeries d) (hf : ∀ i, Convergent (f i))
    (h0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, AtRadius (f i) r ∧ mass (f i) r ≤ ε := by
  obtain ⟨α, hα, C, hC, hb⟩ := common_bounds f hf
  let r := (2 * C)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hCr : C * r = 1 / 2 := by dsimp [r]; field_simp
  have hs : ∀ i, AtRadius (f i) r := fun i =>
    bound_radius (hb i) hα.le hr.le (by rw [hCr]; norm_num) (by rw [hCr]; norm_num)
  let M := ∑ i, mass (f i) r
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => mass_nonnegative (f i) hr.le
  let t := min 1 (ε / (M + 1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  refine ⟨t * r, mul_pos ht hr, ?_⟩
  intro i
  refine ⟨(hs i).shrink (by positivity) (by nlinarith), ?_⟩
  have hi : mass (f i) r ≤ M := Finset.single_le_sum
    (fun j _ => mass_nonnegative (f j) hr.le) (Finset.mem_univ i)
  have hte : t * (M + 1) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  exact (mass_scale_zero (hs i) (h0 i) hr.le ht.le ht1).trans (by nlinarith)

end Lax825748Proofs.WeightedMass
