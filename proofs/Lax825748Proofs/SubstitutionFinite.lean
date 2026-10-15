import Lax825748Proofs.AnnihilatorExt
import Lax825748Proofs.TriangularSystem
import Lax825748Proofs.Annihilator

noncomputable section

namespace Lax825748Proofs.SubstitutionFinite

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.Shuffle Lax825748.ShuffleIdentities Lax825748.Monomials
open Lax825748.FormalSeries
open scoped BigOperators

abbrev Index := TriangularSystem.Index

def polynomialSubstitution {X : Type} {d : ℕ} (S : Fin d → NCSeries X) :
    MvPolynomial (Fin d) ℝ →ₗ[ℝ] NCSeries X :=
  (Finsupp.linearCombination ℝ (fun I : Index d => shuffleMonomial S I)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

theorem polynomialSubstitution_apply {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (p : MvPolynomial (Fin d) ℝ) (w : Word X) :
    polynomialSubstitution S p w = (AddMonoidAlgebra.coeff p).sum
      (fun I a => a * shuffleMonomial S I w) := by
  simp [polynomialSubstitution, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

@[simp] theorem polynomialSubstitution_monomial {X : Type} {d : ℕ}
    (S : Fin d → NCSeries X) (I : Index d) (a : ℝ) :
    polynomialSubstitution S (MvPolynomial.monomial I a) = a • shuffleMonomial S I := by
  simp [polynomialSubstitution, MvPolynomial.monomial, Finsupp.linearCombination_apply]

def finiteSubstitution {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (f : StateSeries d) (n : ℕ) : NCSeries X :=
  ∑ I ∈ TriangularSystem.indices n, MvPowerSeries.coeff I f • shuffleMonomial S I

theorem substitute_eq_finite {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (f : StateSeries d) (w : Word X) :
    substituteShuffle S f w = finiteSubstitution S f (w.toList.length + 1) w := by
  rw [substituteShuffle, ← polynomialSubstitution_apply]
  change polynomialSubstitution S (MvPowerSeries.truncFinset ℝ
    (TriangularSystem.indices (w.toList.length + 1)) f) w = _
  rw [MvPowerSeries.truncFinset_apply, map_sum]
  simp only [polynomialSubstitution_monomial, finiteSubstitution]

theorem word_letters {X : Type} (w : Word X) :
    (List.ofFn fun i : Fin w.toList.length => letter (w.toList.get i)).prod =
      wordPolynomial w := by
  induction w using FreeMonoid.recOn with
  | one => rfl
  | of_mul x w ih =>
    simpa [FreeMonoid.toList_of_mul, List.ofFn_succ,
      List.prod_cons, Series.word_mul, letter, List.get_eq_getElem] using
      congrArg (fun P => letter x * P) ih

theorem monomial_vanishes {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (I : Index d) (w : Word X)
    (h : w.toList.length < I.degree) : shuffleMonomial S I w = 0 := by
  rw [← Series.pairing_word (shuffleMonomial S I) w, MonomialLists.labels_shuffle,
    ← word_letters w]
  apply Lax825748.ShuffleIdentities.vanishing
    (by simpa only [TriangularSystem.degree_eq_total] using h)
    (fun k => S (MonomialLists.labels I k)) (fun k => hS _) 
    (fun k => ⟨letter (w.toList.get k), LieSubalgebra.subset_lieSpan
      (by exact ⟨_, rfl⟩)⟩)

theorem finiteSubstitution_stable {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (f : StateSeries d) (w : Word X) {m n : ℕ}
    (hm : w.toList.length < m) (hn : w.toList.length < n) :
    finiteSubstitution S f m w = finiteSubstitution S f n w := by
  suffices hh : ∀ a b : ℕ, w.toList.length < a → a ≤ b →
      finiteSubstitution S f a w = finiteSubstitution S f b w by
    rcases le_total m n with h | h
    · exact hh m n hm h
    · exact (hh n m hn h).symm
  intro a b ha hab
  simp only [finiteSubstitution, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_subset (TriangularSystem.indices_mono hab)
  intro I _ hI
  rw [monomial_vanishes S hS I w (by
    have : ¬ I.degree < a := fun h => hI (TriangularSystem.mem_indices.mpr h)
    omega), mul_zero]

theorem substitute_eq_finite_of_lt {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (f : StateSeries d) (w : Word X) {n : ℕ}
    (hn : w.toList.length < n) : substituteShuffle S f w = finiteSubstitution S f n w := by
  rw [substitute_eq_finite]
  exact finiteSubstitution_stable S hS f w (Nat.lt_succ_self _) hn

def polynomialCutoff {X : Type} (Q : NCPolynomial X) : ℕ :=
  Q.coeff.support.sup (fun w => w.toList.length + 1)

theorem pairing_substitute_finite {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (hS : ∀ i, S i 1 = 0) (f : StateSeries d) (Q : NCPolynomial X) {n : ℕ}
    (hn : polynomialCutoff Q ≤ n) :
    pairing (substituteShuffle S f) Q = pairing (finiteSubstitution S f n) Q := by
  apply Finsupp.sum_congr
  intro w hw
  have hle : w.toList.length + 1 ≤ polynomialCutoff Q :=
    Finset.le_sup (s := Q.coeff.support) (f := fun w => w.toList.length + 1) hw
  rw [substitute_eq_finite_of_lt S hS f w (n := n) (by omega)]

theorem pairing_finite {X : Type} {d : ℕ} (S : Fin d → NCSeries X)
    (f : StateSeries d) (Q : NCPolynomial X) (n : ℕ) :
    pairing (finiteSubstitution S f n) Q = ∑ I ∈ TriangularSystem.indices n,
      MvPowerSeries.coeff I f * pairing (shuffleMonomial S I) Q := by
  classical
  unfold finiteSubstitution
  induction TriangularSystem.indices (d := d) n using Finset.induction_on with
  | empty => simp [pairing]
  | @insert I s hi ih => simp [Finset.sum_insert hi, Series.pairing_add_series,
      Series.pairing_smul_series, ih]

theorem shuffle_family_ann {X : Type} {p : ℕ} (K : LieSubalgebraOfPolynomials X)
    (S : Fin p → NCSeries X) (hS : ∀ i, InAnnihilator K (S i)) :
    InAnnihilator K (shuffleList (List.ofFn S)) := by
  intro Q hQ
  rw [Lax825748.ShuffleIdentities.pairing_coproduct]
  have hh := Annihilator.annihilator_coproduct K S hS Q hQ 1
  change ShuffleTensor.tensorPairingLinear S (coproduct p Q) = 0
  simpa only [one_mul] using hh

theorem monomial_ann {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (S : Fin d → NCSeries X) (hS : ∀ i, InAnnihilator K (S i)) (I : Index d) :
    InAnnihilator K (shuffleMonomial S I) := by
  rw [MonomialLists.labels_shuffle]
  exact shuffle_family_ann K _ (fun i => hS _)

theorem substitute_ann {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (S : Fin d → NCSeries X) (hS0 : ∀ i, S i 1 = 0)
    (hS : ∀ i, InAnnihilator K (S i)) (f : StateSeries d) :
    InAnnihilator K (substituteShuffle S f) := by
  intro Q hQ
  rw [pairing_substitute_finite S hS0 f Q (le_refl _), pairing_finite]
  apply Finset.sum_eq_zero
  intro I _
  rw [monomial_ann K S hS I Q hQ, mul_zero]

end Lax825748Proofs.SubstitutionFinite
