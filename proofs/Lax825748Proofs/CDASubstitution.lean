import Lax825748Proofs.GeneralCoordinates
import Lax825748Proofs.CDAAlgebra

noncomputable section
namespace Lax825748Proofs.CDASubstitution

open Lax825748.Series Lax825748.Annihilator Lax825748.FormalSeries
open Lax825748.Monomials

theorem rename_agree {k m n : ℕ} (e : Fin k ↪ Fin m)
    (f g : StateSeries k) (h : Lax825748.FormalSeries.AgreeBelow n f g) :
    Lax825748.FormalSeries.AgreeBelow n (MvPowerSeries.rename e f) (MvPowerSeries.rename e g) := by
  classical
  intro I hI
  by_cases hmem : I ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨J, rfl⟩ := hmem
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename,
      MvPowerSeries.coeff_embDomain_rename]
    apply h J
    simpa only [← TriangularSystem.degree_eq_total, Finsupp.degree_mapDomain] using hI
  · rw [MvPowerSeries.coeff_rename_eq_zero e f hmem,
      MvPowerSeries.coeff_rename_eq_zero e g hmem]

theorem substitute_rename_polynomial {X : Type} {k m : ℕ}
    (S : Fin m → NCSeries X) (hS : ∀ i, S i 1 = 0) (e : Fin k ↪ Fin m)
    (p : MvPolynomial (Fin k) ℝ) :
    substituteShuffle S (MvPowerSeries.rename e p.toMvPowerSeries) =
      substituteShuffle (fun i => S (e i)) p.toMvPowerSeries := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.coe_C, MvPowerSeries.rename_C,
      SubstitutionBasic.substitute_C S hS,
      SubstitutionBasic.substitute_C _ (fun i => hS (e i))]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, SubstitutionAlgebra.substitute_add, hp, hq]
  | mul_X p i hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, MvPowerSeries.rename_X,
      SubstitutionAlgebra.substitute_mul S hS,
      SubstitutionAlgebra.substitute_mul _ (fun i => hS (e i)),
      SubstitutionBasic.substitute_X S hS,
      SubstitutionBasic.substitute_X _ (fun i => hS (e i)), hp]

theorem substitute_rename {X : Type} {k m : ℕ}
    (S : Fin m → NCSeries X) (hS : ∀ i, S i 1 = 0) (e : Fin k ↪ Fin m)
    (f : StateSeries k) :
    substituteShuffle S (MvPowerSeries.rename e f) =
      substituteShuffle (fun i => S (e i)) f := by
  funext w
  let n := w.toList.length + 1
  let p := MvPowerSeries.truncTotal n f
  have hp : Lax825748.FormalSeries.AgreeBelow n f p.toMvPowerSeries :=
    ContinuousDerivations.trunc_agree f le_rfl
  calc
    substituteShuffle S (MvPowerSeries.rename e f) w =
        substituteShuffle S (MvPowerSeries.rename e p.toMvPowerSeries) w :=
      CoordinateContinuity.substitute_agree S _ _ (rename_agree e f _ hp) w (Nat.lt_succ_self _)
    _ = substituteShuffle (fun i => S (e i)) p.toMvPowerSeries w :=
      congrFun (substitute_rename_polynomial S hS e p) w
    _ = substituteShuffle (fun i => S (e i)) f w :=
      (CoordinateContinuity.substitute_agree _ _ _ hp w (Nat.lt_succ_self _)).symm

end Lax825748Proofs.CDASubstitution
