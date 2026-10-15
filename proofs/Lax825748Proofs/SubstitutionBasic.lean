import Lax825748Proofs.SubstitutionAlgebra
import Lax825748Proofs.Projection

noncomputable section
namespace Lax825748Proofs.SubstitutionBasic

open Lax825748.Series Lax825748.Shuffle Lax825748.ShuffleIdentities
open Lax825748.Annihilator Lax825748.FormalSeries Lax825748.Monomials
open SubstitutionFinite TriangularSystem CoordinateContinuity
open scoped BigOperators

theorem monomial_zero {X : Type} {d : ℕ} (S : Fin d → NCSeries X) :
    shuffleMonomial S (0 : Fin d →₀ ℕ) = constantSeries 1 := by
  rw [MonomialLists.labels_shuffle]
  simp [totalDegree, shuffleList]

theorem monomial_single {X : Type} {d : ℕ} (S : Fin d → NCSeries X) (i : Fin d) :
    shuffleMonomial S (Finsupp.single i 1 : Fin d →₀ ℕ) = S i := by
  rw [MonomialLists.labels_shuffle]
  have he := congrArg (List.map S) (MonomialLists.ofFn_labels (Finsupp.single i 1 : Fin d →₀ ℕ))
  simp only [List.map_ofFn, Function.comp_def, CanonicalCoordinates.labelsList_single,
    List.map_cons, List.map_nil] at he
  rw [he]
  exact (Lax825748.Shuffle.commutative _ _).trans (Lax825748.Shuffle.unit _)

theorem scalar_constant {X : Type} (a : ℝ) : a • (constantSeries 1 : NCSeries X) = constantSeries a := by
  funext w
  by_cases h : w = 1 <;> simp [constantSeries, h]

theorem substitute_C {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (a : ℝ) : substituteShuffle S (MvPowerSeries.C a) = constantSeries a := by
  rw [← MvPolynomial.coe_C, SubstitutionAlgebra.substitute_polynomial S hS,
    MvPolynomial.C_apply, polynomialSubstitution_monomial, monomial_zero, scalar_constant]

theorem substitute_X {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (i : Fin d) : substituteShuffle S (MvPowerSeries.X i) = S i := by
  rw [← MvPolynomial.coe_X, SubstitutionAlgebra.substitute_polynomial S hS]
  change polynomialSubstitution S (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  rw [polynomialSubstitution_monomial, one_smul, monomial_single]

theorem substitute_smul {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (a : ℝ) (f : StateSeries d) : substituteShuffle S (a • f) = a • substituteShuffle S f := by
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [substitute_eq_finite, substitute_eq_finite]
  simp [finiteSubstitution, map_smul, Finset.mul_sum, mul_assoc]

theorem substitute_zero {X : Type} {d : ℕ} (S : Fin d → NCSeries X) :
    substituteShuffle S (0 : StateSeries d) = 0 := by
  rw [← zero_smul ℝ (0 : StateSeries d), substitute_smul, zero_smul]

theorem substitute_injective {X : Type} {d : ℕ}
    (P : Fin d → Lax825748.LieRank.LiePolynomial X) (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (hPBW : IsPBWCoordinateFamily P S) : Function.Injective (substituteShuffle S) := by
  intro f g hfg
  have hh := congrArg (moments P) hfg
  simpa only [moments_substitute P S hS hSP hPBW] using hh

theorem substitute_moments {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → Lax825748.LieRank.LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S)
    (hPBW : IsPBWCoordinateFamily P S) (T : NCSeries X) (hT : InAnnihilator K T) :
    substituteShuffle S (moments P T) = T :=
  (Lax825748.Projection.projection K P hP S hS hPBW).2.2.2.2.2 T hT

theorem substitute_empty {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (f : StateSeries d) :
    substituteShuffle S f 1 = MvPowerSeries.constantCoeff f := by
  have hh : Lax825748.FormalSeries.AgreeBelow 1 f (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by
    intro I hI
    have hI0 : I = 0 := (Finsupp.degree_eq_zero_iff I).mp (by
      have hd := degree_eq_total I; omega)
    subst I
    simp
  have he := CoordinateContinuity.substitute_agree S _ _ hh 1 (by simp)
  rw [substitute_C S hS] at he
  simpa [constantSeries] using he

end Lax825748Proofs.SubstitutionBasic
