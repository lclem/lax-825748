import Lax825748.Projection
import Lax825748Proofs.CoordinateContinuity
import Lax825748Proofs.MomentComparison

noncomputable section
namespace Lax825748Proofs.Projection

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator Lax825748.Monomials
open Lax825748.Shuffle Lax825748.Projection
open CoordinateContinuity

theorem theta_ann {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (S : Fin d → NCSeries X)
    (hS : IsCoordinateFamily K P S) (T : NCSeries X) :
    InAnnihilator K (theta P S T) :=
  SubstitutionFinite.substitute_ann K S hS.1 hS.2.1 _

theorem theta_moment {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (hPBW : IsPBWCoordinateFamily P S) (T : NCSeries X) (I : Fin d → ℕ) :
    pairing (theta P S T) (orderedPowers (fun i => (P i).val) I) =
      pairing T (orderedPowers (fun i => (P i).val) I) := by
  let J := Finsupp.equivFunOnFinite.symm I
  have hJI : (J : Fin d → ℕ) = I := Finsupp.equivFunOnFinite.apply_symm_apply I
  rw [← hJI]
  change pairing (substituteShuffle S (moments P T)) _ = _
  rw [PBWMoments.substitution_moment P S hS hSP hPBW]
  change (_ / (multiFactorial J : ℝ)) * _ = _
  apply div_mul_cancel₀
  exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (J i))

theorem constant_ann {X : Type} (K : LieSubalgebraOfPolynomials X) (a : ℝ) :
    InAnnihilator K (constantSeries a) := by
  have hh := SubstitutionFinite.shuffle_family_ann K (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i)
  have hc : constantSeries a = a • (shuffleList (List.ofFn fun i : Fin 0 => (Fin.elim0 i : NCSeries X))) := by
    funext w
    simp [constantSeries, shuffleList, Pi.smul_apply, smul_eq_mul]
  rw [hc]
  intro Q hQ
  rw [Series.pairing_smul_series, hh Q hQ, mul_zero]

/--
---
conclusion: Lax825748.Projection.projection
---
The PBW expansion preserves complementary moments. Those moments determine
annihilator series and determine the moments of shuffle products by the
primitive coproduct. Finite truncations give formal continuity.
-/
theorem projection {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S)
    (hPBW : IsPBWCoordinateFamily P S) :
  Lax825748.Series.FormallyContinuous (theta P S) ∧
  (∀ a : ℝ, theta P S (constantSeries a) = constantSeries a) ∧
  (∀ T U, theta P S (T + U) = theta P S T + theta P S U) ∧
  (∀ T U, theta P S (shuffle T U) = shuffle (theta P S T) (theta P S U)) ∧
  (∀ T, InAnnihilator K (theta P S T)) ∧
  (∀ T, InAnnihilator K T → theta P S T = T) := by
  have hfix : ∀ T, InAnnihilator K T → theta P S T = T := by
    intro T hT
    obtain ⟨f, hf, hc⟩ := Lax825748.Annihilator.pbw_expansion K P hP S hS hPBW T hT
    have hm : moments P T = f := by ext I; exact (hc I).symm
    change substituteShuffle S (moments P T) = T
    rw [hm, hf]
  have hm := theta_moment P S hS.1 hS.2.2 hPBW
  refine ⟨?_, fun a => hfix _ (constant_ann K a), ?_, ?_, theta_ann K P S hS, hfix⟩
  · intro n
    obtain ⟨m, hm⟩ := moments_agree P n
    exact ⟨m, fun T U h => substitute_agree S _ _ (hm T U h)⟩
  · intro T U
    apply AnnihilatorExt.annihilator_ext K P hP _ _ (theta_ann K P S hS _)
    · intro Q hQ
      rw [Series.pairing_add_series, theta_ann K P S hS T Q hQ,
        theta_ann K P S hS U Q hQ, add_zero]
    · intro I
      rw [hm, Series.pairing_add_series, Series.pairing_add_series, hm, hm]
  · intro T U
    apply AnnihilatorExt.annihilator_ext K P hP _ _ (theta_ann K P S hS _)
      (Lax825748.Annihilator.closed_shuffle K _ _ (theta_ann K P S hS _) (theta_ann K P S hS _))
    intro I
    rw [hm]
    exact MomentComparison.shuffle_moments P T U _ _ (fun I => (hm T I).symm)
      (fun I => (hm U I).symm) I

end Lax825748Proofs.Projection
