import Lax825748Proofs.PBWMoments

noncomputable section
namespace Lax825748Proofs.CoordinateContinuity

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator Lax825748.Monomials
open SubstitutionFinite TriangularSystem
open scoped BigOperators

def moments {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X) (T : NCSeries X) :
    Lax825748.FormalSeries.StateSeries d :=
  fun I => pairing T (orderedPowers (fun j => (P j).val) I) / (multiFactorial I : ℝ)

theorem substitute_agree {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    {n : ℕ} (f g : Lax825748.FormalSeries.StateSeries d)
    (h : Lax825748.FormalSeries.AgreeBelow n f g) :
    Lax825748.Series.AgreeBelow n (substituteShuffle S f) (substituteShuffle S g) := by
  intro w hw
  rw [substitute_eq_finite, substitute_eq_finite]
  simp only [finiteSubstitution, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [h I (by have := mem_indices.mp hI; rw [degree_eq_total] at this; omega)]

theorem pairing_agree {X : Type} (T U : NCSeries X) (Q : NCPolynomial X) {n : ℕ}
    (h : Lax825748.Series.AgreeBelow n T U) (hn : polynomialCutoff Q ≤ n) :
    pairing T Q = pairing U Q := by
  apply Finsupp.sum_congr
  intro w hw
  have hh : w.toList.length + 1 ≤ polynomialCutoff Q :=
    Finset.le_sup (s := Q.coeff.support) (f := fun w => w.toList.length + 1) hw
  rw [h w (by omega)]

theorem moments_agree {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X) (n : ℕ) :
    ∃ m, ∀ T U : NCSeries X, Lax825748.Series.AgreeBelow m T U →
      Lax825748.FormalSeries.AgreeBelow n (moments P T) (moments P U) := by
  classical
  let m := (indices (d := d) n).sup fun I =>
    polynomialCutoff (orderedPowers (fun j => (P j).val) I)
  refine ⟨m, ?_⟩
  intro T U h I hI
  change pairing T _ / _ = pairing U _ / _
  have hle : polynomialCutoff (orderedPowers (fun j => (P j).val) I) ≤ m :=
    Finset.le_sup (s := indices n)
      (f := fun J => polynomialCutoff (orderedPowers (fun j => (P j).val) J))
      (mem_indices.mpr (by simpa only [degree_eq_total] using hI))
  rw [pairing_agree T U _ h hle]

theorem moments_substitute {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (hPBW : IsPBWCoordinateFamily P S) (f : Lax825748.FormalSeries.StateSeries d) :
    moments P (substituteShuffle S f) = f := by
  ext I
  change pairing (substituteShuffle S f) _ / _ = MvPowerSeries.coeff I f
  rw [PBWMoments.substitution_moment P S hS hSP hPBW]
  apply mul_div_cancel_right₀
  exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (I i))

end Lax825748Proofs.CoordinateContinuity
