import Lax825748Proofs.CoordinateContinuity

noncomputable section
namespace Lax825748Proofs.InverseContinuity

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator Lax825748.Monomials
open Lax825748.FormalSeries
open TriangularSystem FormalCoordinates CoordinateContinuity
open scoped BigOperators

theorem coeff_agree {X : Type} {d n : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (f g : StateSeries d)
    (hm : ∀ I : Index d, I.degree < n →
      pairing (substituteShuffle S f) (orderedPowers (fun i => (P i).val) I) =
      pairing (substituteShuffle S g) (orderedPowers (fun i => (P i).val) I)) :
    Lax825748.FormalSeries.AgreeBelow n f g := by
  have hA := matrix_triangular P S hS hSP
  have he : ∀ k, ∀ I : Index d, I.degree = k → k < n →
      MvPowerSeries.coeff I f = MvPowerSeries.coeff I g := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro I hI hk
      apply (mul_left_inj' (hA.2 I)).mp
      have hh := hm I (by omega)
      rw [pairing_substitute P S hS hSP, pairing_substitute P S hS hSP,
        row_split _ hA, row_split _ hA] at hh
      have hlow : (∑ J ∈ indices I.degree, MvPowerSeries.coeff J f * matrix P S I J) =
          (∑ J ∈ indices I.degree, MvPowerSeries.coeff J g * matrix P S I J) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [ih J.degree (by have := mem_indices.mp hJ; omega) J rfl
          (by have := mem_indices.mp hJ; omega)]
      linarith
  intro I hI
  exact he I.degree I rfl (by simpa only [degree_eq_total] using hI)

theorem substitute_inverse_continuous {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0) :
    ∀ n, ∃ m, ∀ f g : StateSeries d,
      Lax825748.Series.AgreeBelow m (substituteShuffle S f) (substituteShuffle S g) →
      Lax825748.FormalSeries.AgreeBelow n f g := by
  intro n
  obtain ⟨m, hm⟩ := moments_agree P n
  refine ⟨m, ?_⟩
  intro f g hfg
  apply coeff_agree P S hS hSP f g
  intro I hI
  have hh := hm _ _ hfg I (by simpa only [degree_eq_total] using hI)
  change pairing _ _ / (multiFactorial I : ℝ) = pairing _ _ / _ at hh
  apply (div_left_inj' (by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (I i)))).mp hh

end Lax825748Proofs.InverseContinuity
