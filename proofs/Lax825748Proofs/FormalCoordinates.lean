import Lax825748Proofs.SubstitutionFinite

noncomputable section

namespace Lax825748Proofs.FormalCoordinates

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.ShuffleIdentities Lax825748.Monomials Lax825748.FormalSeries
open SubstitutionFinite TriangularSystem
open scoped BigOperators

def matrix {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (I J : TriangularSystem.Index d) : ℝ :=
  pairing (shuffleMonomial S J) (orderedPowers (fun i => (P i).val) I)

theorem matrix_triangular {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0) :
    IsTriangular (matrix P S) := by
  classical
  constructor
  · intro I J hdeg hne
    unfold matrix
    rw [(Lax825748.ShuffleIdentities.triangular_pairing S P hS hSP J I).2
      (by simpa only [degree_eq_total] using hdeg.symm)]
    exact if_neg (fun he => hne (DFunLike.coe_injective he).symm)
  · intro I
    unfold matrix
    rw [(Lax825748.ShuffleIdentities.triangular_pairing S P hS hSP I I).2 rfl,
      if_pos rfl]
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (I i))

theorem pairing_substitute {X : Type} {d : ℕ} (P : Fin d → LiePolynomial X)
    (S : Fin d → NCSeries X) (hS : ∀ i, S i 1 = 0)
    (hSP : ∀ i j, pairing (S i) (P j).val = if i = j then 1 else 0)
    (f : StateSeries d) (I : TriangularSystem.Index d) :
    pairing (substituteShuffle S f) (orderedPowers (fun i => (P i).val) I) =
      ∑ J ∈ indices (I.degree + 1), MvPowerSeries.coeff J f * matrix P S I J := by
  classical
  let Q := orderedPowers (fun i => (P i).val) I
  let n := max (polynomialCutoff Q) (I.degree + 1)
  rw [pairing_substitute_finite S hS f Q (le_max_left _ _), pairing_finite]
  symm
  apply Finset.sum_subset (indices_mono (le_max_right _ _))
  intro J _ hJ
  have hd : I.degree < J.degree := by
    have hn : ¬ J.degree < I.degree + 1 := fun h => hJ (mem_indices.mpr h)
    omega
  unfold matrix
  rw [(Lax825748.ShuffleIdentities.triangular_pairing S P hS hSP J I).1
    (by simpa only [degree_eq_total] using hd), mul_zero]

/--
---
conclusion: Lax825748.Annihilator.formal_coordinates
---
The finite coefficient system is triangular with nonzero factorial diagonal.
Solve it degree by degree, then use the adapted PBW basis to identify series
in the annihilator from their complementary moments.
-/
theorem formal_coordinates {X : Type} {d : ℕ} (K : LieSubalgebraOfPolynomials X)
    (P : Fin d → LiePolynomial X) (hP : IsComplement K P)
    (S : Fin d → NCSeries X) (hS : IsCoordinateFamily K P S) :
    ∀ T : NCSeries X, InAnnihilator K T ↔ ∃! f : StateSeries d, substituteShuffle S f = T := by
  intro T
  constructor
  · intro hT
    let b : TriangularSystem.Index d → ℝ := fun I => pairing T (orderedPowers (fun i => (P i).val) I)
    let f : StateSeries d := solve (matrix P S) b
    have hA := matrix_triangular P S hS.1 hS.2.2
    have hf : substituteShuffle S f = T := by
      apply AnnihilatorExt.annihilator_ext K P hP _ T (substitute_ann K S hS.1 hS.2.1 f) hT
      intro I
      let J : TriangularSystem.Index d := Finsupp.equivFunOnFinite.symm I
      have hJI : (J : Fin d → ℕ) = I := Finsupp.equivFunOnFinite.apply_symm_apply I
      rw [← hJI, pairing_substitute P S hS.1 hS.2.2]
      exact solve_rows (matrix P S) hA b J
    refine ⟨f, hf, ?_⟩
    intro g hg
    apply solution_unique (matrix P S) hA b
    · intro I
      change (∑ J ∈ indices (I.degree + 1), MvPowerSeries.coeff J g * matrix P S I J) = b I
      rw [← pairing_substitute P S hS.1 hS.2.2, hg]
    · intro I
      exact solve_rows (matrix P S) hA b I
  · rintro ⟨f, hf, _⟩
    rw [← hf]
    exact substitute_ann K S hS.1 hS.2.1 f

end Lax825748Proofs.FormalCoordinates
