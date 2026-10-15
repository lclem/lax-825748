import Lax825748Proofs.ShuffleAlgebra
import Lax825748Proofs.CoordinateContinuity

noncomputable section
namespace Lax825748Proofs.SubstitutionAlgebra

open Lax825748.Series Lax825748.Shuffle Lax825748.ShuffleIdentities
open Lax825748.Annihilator Lax825748.FormalSeries Lax825748.Monomials
open SubstitutionFinite TriangularSystem
open scoped BigOperators

theorem unshuffles_length {X : Type} (l : List X) (a b : List X)
    (h : (a,b) ∈ unshuffles l) : a.length + b.length = l.length := by
  induction l generalizing a b with
  | nil => simpa [unshuffles] using h
  | cons x l ih =>
    obtain ⟨⟨u,v⟩, huv, he⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    have hh := ih u v huv
    rcases he with he | he
    · have hfst := congrArg Prod.fst he
      have hsnd := congrArg Prod.snd he
      change a = x :: u at hfst
      change b = v at hsnd
      simp only [hfst, hsnd, List.length_cons]
      omega
    · have hfst := congrArg Prod.fst he
      have hsnd := congrArg Prod.snd he
      change a = u at hfst
      change b = x :: v at hsnd
      simp only [hfst, hsnd, List.length_cons]
      omega

theorem shuffle_agree {X : Type} {n : ℕ} (S T U V : NCSeries X)
    (hSU : Lax825748.Series.AgreeBelow n S U) (hTV : Lax825748.Series.AgreeBelow n T V) :
    Lax825748.Series.AgreeBelow n (shuffle S T) (shuffle U V) := by
  intro w hw
  unfold shuffle
  congr 1
  apply List.map_congr_left
  intro p hp
  have hh := unshuffles_length w.toList p.1 p.2 hp
  rw [hSU _ (by simpa only [FreeMonoid.toList_ofList] using (show p.1.length < n by omega)),
    hTV _ (by simpa only [FreeMonoid.toList_ofList] using (show p.2.length < n by omega))]

theorem polynomial_agree {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (p q : MvPolynomial (Fin d) ℝ) {n : ℕ}
    (h : ∀ I : Fin d →₀ ℕ, I.degree < n → MvPolynomial.coeff I p = MvPolynomial.coeff I q)
    (w : Word X) (hw : w.toList.length < n) :
    polynomialSubstitution S p w = polynomialSubstitution S q w := by
  have hz : polynomialSubstitution S (p - q) w = 0 := by
    rw [polynomialSubstitution_apply]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro I _
    change MvPolynomial.coeff I (p - q) * _ = 0
    by_cases hI : I.degree < n
    · rw [MvPolynomial.coeff_sub, h I hI, sub_self, zero_mul]
    · rw [monomial_vanishes S hS I w (by omega), mul_zero]
  have hh : polynomialSubstitution S p w - polynomialSubstitution S q w = 0 := by
    simpa only [map_sub, Pi.sub_apply] using hz
  exact sub_eq_zero.mp hh

theorem polynomial_trunc {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (f : StateSeries d) (n : ℕ) :
    polynomialSubstitution S (MvPowerSeries.truncTotal n f) = finiteSubstitution S f n := by
  change polynomialSubstitution S (MvPowerSeries.truncFinset ℝ (indices n) f) = _
  rw [MvPowerSeries.truncFinset_apply, map_sum]
  simp only [polynomialSubstitution_monomial, finiteSubstitution]

theorem substitute_trunc {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (f : StateSeries d) {n : ℕ} (w : Word X)
    (hw : w.toList.length < n) :
    substituteShuffle S f w = polynomialSubstitution S (MvPowerSeries.truncTotal n f) w := by
  rw [polynomial_trunc]
  exact substitute_eq_finite_of_lt S hS f w hw

theorem substitute_mul {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (f g : StateSeries d) :
    substituteShuffle S (f * g) = shuffle (substituteShuffle S f) (substituteShuffle S g) := by
  funext w
  let n := w.toList.length + 1
  have hw : w.toList.length < n := Nat.lt_succ_self _
  rw [substitute_trunc S hS (f * g) w hw]
  have hp := polynomial_agree S hS (MvPowerSeries.truncTotal n (f * g))
    (MvPowerSeries.truncTotal n f * MvPowerSeries.truncTotal n g)
    (fun I hI => (MvPowerSeries.coeff_truncTotal _ hI).trans
      (MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hI).symm) w hw
  rw [hp, ShuffleAlgebra.polynomial_mul]
  exact shuffle_agree _ _ _ _ (fun u hu => (substitute_trunc S hS f u hu).symm)
    (fun u hu => (substitute_trunc S hS g u hu).symm) w hw

theorem substitute_add {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (f g : StateSeries d) :
    substituteShuffle S (f + g) = substituteShuffle S f + substituteShuffle S g := by
  funext w
  simp only [Pi.add_apply]
  rw [substitute_eq_finite, substitute_eq_finite, substitute_eq_finite]
  simp [finiteSubstitution, map_add, add_smul, Finset.sum_add_distrib]

theorem substitute_polynomial {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (p : MvPolynomial (Fin d) ℝ) :
    substituteShuffle S p.toMvPowerSeries = polynomialSubstitution S p := by
  funext w
  rw [substitute_trunc S hS _ w (Nat.lt_succ_self _)]
  exact polynomial_agree S hS _ p (fun I hI => by
    rw [MvPowerSeries.coeff_truncTotal _ hI, MvPolynomial.coeff_coe]) w (Nat.lt_succ_self _)

end Lax825748Proofs.SubstitutionAlgebra
