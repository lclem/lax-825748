import Lax825748Proofs.ShuffleFinite
import Lax825748.CDA
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Lax825748Proofs.CDAAmbient

open Lax825748.Series Lax825748.LieRank Lax825748.Annihilator
open Lax825748.Shuffle Lax825748.ShuffleIdentities Lax825748.ShuffleFinite
open scoped BigOperators

theorem lie_pairing_shuffle {X : Type} (S T : NCSeries X) (P : LiePolynomial X) :
    pairing (shuffle S T) P.val = pairing S P.val * T 1 + S 1 * pairing T P.val := by
  have hslot (Q : NCPolynomial X) :
      ShuffleTensor.tensorPairingLinear ![S, T] (Coproduct.slotHom (0 : Fin 2) Q) =
        pairing S Q * T 1 ∧
      ShuffleTensor.tensorPairingLinear ![S, T] (Coproduct.slotHom (1 : Fin 2) Q) =
        S 1 * pairing T Q := by
    induction Q using MonoidAlgebra.induction_on with
    | of w =>
      change ShuffleTensor.tensorPairingLinear ![S,T]
          (Coproduct.slotHom 0 (MonoidAlgebra.single w 1)) = _ ∧
        ShuffleTensor.tensorPairingLinear ![S,T]
          (Coproduct.slotHom 1 (MonoidAlgebra.single w 1)) = _
      simp [Coproduct.slotWord, Fin.prod_univ_two]
    | add Q R hQ hR => simp [hQ, hR, add_mul, mul_add]
    | smul a Q hQ => simp [hQ, mul_assoc, mul_left_comm]
  have hp := Lax825748.ShuffleIdentities.pairing_coproduct ![S,T] P.val
  have hl : shuffleList (List.ofFn ![S,T]) = shuffle S T := by
    simp [List.ofFn_succ, shuffleList, Lax825748.Shuffle.commutative T, Lax825748.Shuffle.unit]
  rw [hl] at hp
  change _ = ShuffleTensor.tensorPairingLinear ![S,T] (coproduct 2 P.val) at hp
  rw [Lax825748.ShuffleIdentities.lie_primitive, map_sum] at hp
  simpa only [Fin.sum_univ_two, Coproduct.insertFactor_eq,
    (hslot P.val).1, (hslot P.val).2] using hp

def asAlgebra {X : Type} (A : ShuffleSubalgebra X) :
    Subalgebra ℝ (ShuffleAlgebra.Algebra X) where
  carrier := fun a => a ∈ A.toSubmodule
  zero_mem' := A.toSubmodule.zero_mem
  one_mem' := A.one_mem
  add_mem' := A.toSubmodule.add_mem
  mul_mem' := A.shuffle_mem _ _
  algebraMap_mem' a := A.toSubmodule.smul_mem a A.one_mem

theorem monomial_mem {X : Type} {n : ℕ}
    (B : Subalgebra ℝ (ShuffleAlgebra.Algebra X)) (S : Fin n → NCSeries X)
    (hS : ∀ i, S i ∈ B) (I : Fin n → ℕ) : shuffleMonomial S I ∈ B := by
  change shuffleList (List.ofFn fun i => shufflePow (S i) (I i)) ∈ B
  rw [← ShuffleAlgebra.list_prod]
  apply B.list_prod_mem
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  rw [← ShuffleAlgebra.pow_eq]
  exact B.pow_mem (hS i) _

theorem asAlgebra_fg {X : Type} (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A) :
    (asAlgebra A).FG := by
  classical
  obtain ⟨n, S, hS⟩ := hfg
  let B : Subalgebra ℝ (ShuffleAlgebra.Algebra X) :=
    Algebra.adjoin ℝ (Set.range S)
  have hgen (i : Fin n) : S i ∈ A.toSubmodule := by
    rw [hS]
    rw [← SubstitutionBasic.monomial_single S i]
    exact Submodule.subset_span ⟨_, rfl⟩
  have he : B = asAlgebra A := by
    apply le_antisymm
    · exact Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hgen i)
    · intro f hf
      change f ∈ A.toSubmodule at hf
      rw [hS] at hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨I, rfl⟩ := hf
        exact monomial_mem B S (fun i => Algebra.subset_adjoin (Set.mem_range_self i)) I
      | zero => exact B.zero_mem
      | add f g _ _ hf hg => exact B.add_mem hf hg
      | smul a f _ hf => exact B.smul_mem hf a
  exact Subalgebra.fg_def.mpr ⟨Set.range S, Set.finite_range S, he⟩

def liePairing {X : Type} : ShuffleAlgebra.Algebra X →ₗ[ℝ] Module.Dual ℝ (LiePolynomial X) where
  toFun S := (Series.pairingLinear S).comp (liePolynomials X).toSubmodule.subtype
  map_add' S T := by ext P; exact Series.pairing_add_series S T P.val
  map_smul' a S := by ext P; exact Series.pairing_smul_series a S P.val

theorem liePairing_mul {X : Type} (S T : ShuffleAlgebra.Algebra X) :
    liePairing (S * T) = T 1 • liePairing S + S 1 • liePairing T := by
  ext P
  change pairing (shuffle S T) P.val = T 1 * pairing S P.val + S 1 * pairing T P.val
  rw [lie_pairing_shuffle, mul_comm (pairing S P.val)]

def pairingOn {X : Type} (A : ShuffleSubalgebra X) :
    A.toSubmodule →ₗ[ℝ] Module.Dual ℝ (LiePolynomial X) :=
  liePairing.comp A.toSubmodule.subtype

theorem pairing_range_finite {X : Type} (A : ShuffleSubalgebra X)
    (hfg : FinitelyGenerated A) : Module.Finite ℝ (LinearMap.range (pairingOn A)) := by
  classical
  obtain ⟨s, hs⟩ := asAlgebra_fg A hfg
  let E : Submodule ℝ (Module.Dual ℝ (LiePolynomial X)) :=
    Submodule.span ℝ ((liePairing (X := X)) '' (s : Set (ShuffleAlgebra.Algebra X)))
  have hE : ∀ a ∈ asAlgebra A, liePairing a ∈ E := by
    rw [← hs]
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | algebraMap a =>
      have hz : liePairing (algebraMap ℝ (ShuffleAlgebra.Algebra X) a) = 0 := by
        ext P
        change pairing (a • constantSeries 1) P.val = 0
        rw [SubstitutionBasic.scalar_constant]
        exact ResidualCoordinates.constant_pairing_lie a P
      rw [hz]
      exact E.zero_mem
    | add a b _ _ ha hb => simpa only [map_add] using E.add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [liePairing_mul]
      exact E.add_mem (E.smul_mem _ ha) (E.smul_mem _ hb)
  have hrange : LinearMap.range (pairingOn A) ≤ E := by
    rintro _ ⟨a, rfl⟩
    exact hE a.val a.property
  let : Module.Finite ℝ E := Module.Finite.span_of_finite ℝ (s.finite_toSet.image _)
  let F : LinearMap.range (pairingOn A) →ₗ[ℝ] E := Submodule.inclusion hrange
  exact FiniteDimensional.of_injective (K := ℝ)
    (V := LinearMap.range (pairingOn A)) (V₂ := E) F (by
    intro a b h
    exact Subtype.ext (congrArg (fun z : E => z.val) h))

def stabilizer {X : Type} (A : ShuffleSubalgebra X) (hs : DerivativeStable A) :
    LieSubalgebraOfPolynomials X where
  carrier := {P | ∀ a ∈ A.toSubmodule, pairing a P.val = 0}
  zero_mem' := by intro a _; simp
  add_mem' := by intro P Q hP hQ a ha; simp [hP a ha, hQ a ha]
  smul_mem' := by intro r P hP a ha; simp [hP a ha]
  lie_mem' := by
    intro P Q hP hQ a ha
    change pairing a (P.val * Q.val - Q.val * P.val) = 0
    change Series.pairingLinear a (_ - _) = 0
    rw [map_sub]
    change pairing a (P.val * Q.val) - pairing a (Q.val * P.val) = 0
    rw [← Series.pairing_right_residual, ← Series.pairing_right_residual,
      hQ _ (ShuffleFinite.residual_mem A hs a ha P.val),
      hP _ (ShuffleFinite.residual_mem A hs a ha Q.val), sub_self]

theorem mem_annihilator {X : Type} (A : ShuffleSubalgebra X) (hs : DerivativeStable A)
    (a : NCSeries X) (ha : a ∈ A.toSubmodule) : InAnnihilator (stabilizer A hs) a := by
  intro P hP
  have hall : ∀ Q ∈ generatedIdeal (stabilizer A hs), ∀ T : NCPolynomial X,
      pairing a (T * Q) = 0 := by
    intro Q hQ
    change Q ∈ Submodule.span (NCPolynomial X) {P | ∃ k : stabilizer A hs, P = k.val.val} at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨q, rfl⟩ := hQ
      intro T
      rw [← Series.pairing_right_residual]
      exact q.property _ (ShuffleFinite.residual_mem A hs a ha T)
    | zero => intro T; simp
    | add Q R _ _ hQ hR => intro T; simp [mul_add, hQ, hR]
    | smul U Q _ hQ => intro T; exact (by
        change pairing a (T * (U * Q)) = 0
        rw [← mul_assoc]
        exact hQ (T * U))
  simpa only [one_mul] using hall P hP 1

theorem basis_lifts {W V : Type} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (F : W →ₗ[ℝ] V) (hF : Function.Surjective F) {k : ℕ}
    (g : Fin k → W) (hi : LinearIndependent ℝ (fun i => F (g i))) :
    ∃ (m : ℕ) (e : Fin k ↪ Fin m) (b : Module.Basis (Fin m) ℝ V) (s : Fin m → W),
      (∀ j, F (s j) = b j) ∧ ∀ i, s (e i) = g i := by
  classical
  let I := hi.linearIndepOn_id.extend (Set.subset_univ _)
  let b₀ : Module.Basis I ℝ V := Module.Basis.extend hi.linearIndepOn_id
  let : Fintype I := FiniteDimensional.fintypeBasisIndex b₀
  let q : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let v : Fin k → I := fun i =>
    ⟨F (g i), Module.Basis.subset_extend hi.linearIndepOn_id (Set.mem_range_self i)⟩
  let e : Fin k ↪ Fin (Fintype.card I) :=
    ⟨fun i => q (v i), fun i j h => hi.injective (congrArg Subtype.val (q.injective h))⟩
  let b : Module.Basis (Fin (Fintype.card I)) ℝ V := b₀.reindex q
  have he (i : Fin k) : b (e i) = F (g i) := by
    simp only [b, Module.Basis.reindex_apply]
    exact (congrArg b₀ (q.symm_apply_apply (v i))).trans
      (Module.Basis.extend_apply_self hi.linearIndepOn_id (v i))
  have hl (j : Fin (Fintype.card I)) : ∃ w : W, F w = b j ∧
      ∀ i, e i = j → w = g i := by
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      exact ⟨g i, (he i).symm, fun l hl => congrArg g (e.injective hl).symm⟩
    · obtain ⟨w, hw⟩ := hF (b j)
      exact ⟨w, hw, fun i hi => False.elim (h ⟨i, hi⟩)⟩
  choose s hs hg using hl
  exact ⟨Fintype.card I, e, b, s, hs, fun i => hg (e i) i rfl⟩

set_option maxHeartbeats 800000 in
theorem ambient_coordinates {X : Type} {k : ℕ}
    (A : ShuffleSubalgebra X) (hfg : FinitelyGenerated A) (hs : DerivativeStable A)
    (G : Fin k → NCSeries X) (hzero : ∀ i, G i 1 = 0)
    (P : Fin k → LiePolynomial X)
    (hpair : ∀ i j, pairing (G i) (P j).val = if i = j then 1 else 0)
    (hmem : ∀ i, G i ∈ A.toSubmodule) :
    ∃ (m : ℕ) (e : Fin k ↪ Fin m) (K : LieSubalgebraOfPolynomials X)
      (Q : Fin m → LiePolynomial X) (S : Fin m → NCSeries X),
      IsComplement K Q ∧ IsCoordinateFamily K Q S ∧
      (∀ j, S j ∈ A.toSubmodule) ∧ (∀ i, S (e i) = G i) ∧
      ∀ a ∈ A.toSubmodule, InAnnihilator K a := by
  classical
  let E := LinearMap.range (pairingOn A)
  let : Module.Finite ℝ E := pairing_range_finite A hfg
  let F : A.toSubmodule →ₗ[ℝ] E := (pairingOn A).rangeRestrict
  let g : Fin k → A.toSubmodule := fun i => ⟨G i, hmem i⟩
  have hi : LinearIndependent ℝ (fun i => F (g i)) := by
    apply (Fintype.linearIndependent_iff (R := ℝ) (v := fun i : Fin k => F (g i))).mpr
    intro a ha j
    have hh := congrArg (fun z : E => z.val (P j)) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul] at hh
    change (∑ i, a i * pairing (G i) (P j).val) = 0 at hh
    simpa only [hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using hh
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨a, ha⟩ := z.property
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨m, e, b, s, hsF, hsg⟩ :=
    basis_lifts (W := A.toSubmodule) (V := E) F hF g hi
  let S : Fin m → NCSeries X := fun j => (s j).val - constantSeries ((s j).val 1)
  have hS (j : Fin m) : S j ∈ A.toSubmodule :=
    A.toSubmodule.sub_mem (s j).property (ShuffleFinite.constant_mem A _)
  have hSb (j : Fin m) : liePairing (S j) = (b j).val := by
    ext L
    change pairing ((s j).val - constantSeries ((s j).val 1)) L.val = (b j).val L
    rw [ResidualCoordinates.pairing_sub_series, ResidualCoordinates.constant_pairing_lie, sub_zero]
    exact congrArg (fun z : E => z.val L) (hsF j)
  let D : LiePolynomial X →ₗ[ℝ] Module.Dual ℝ E := E.subtype.flip
  have hD : Function.Surjective D := by
    change Function.Surjective E.subtype.flip
    exact (LinearMap.flip_surjective_iff₁ (K := ℝ) (V₁ := E) (V₂ := LiePolynomial X)
      (B := E.subtype)).mpr E.subtype_injective
  choose Q hQ using fun j : Fin m => hD (b.dualBasis j)
  let K := stabilizer A hs
  have hker : K.toSubmodule = LinearMap.ker D := by
    ext L
    change (∀ a ∈ A.toSubmodule, pairing a L.val = 0) ↔ D L = 0
    constructor
    · intro h
      ext z
      obtain ⟨a, ha⟩ := z.property
      change z.val L = 0
      rw [← ha]
      exact h a.val a.property
    · intro h a ha
      exact congrArg (fun z : Module.Dual ℝ E => z (F ⟨a, ha⟩)) h
  have hcomp : IsComplement K Q := by
    change LinearIndependent ℝ (fun i => K.toSubmodule.mkQ (Q i)) ∧
      Submodule.span ℝ (Set.range fun i => K.toSubmodule.mkQ (Q i)) = ⊤
    rw [hker]
    let c := b.dualBasis.map (D.quotKerEquivOfSurjective hD).symm
    have hc (j : Fin m) : c j = (LinearMap.ker D).mkQ (Q j) := by
      rw [Module.Basis.map_apply, ← hQ j,
        LinearMap.quotKerEquivOfSurjective_symm_apply]
      rfl
    have hcfun : (c : Fin m → _) = fun j => (LinearMap.ker D).mkQ (Q j) := funext hc
    rw [← hcfun]
    exact ⟨c.linearIndependent, c.span_eq⟩
  refine ⟨m, e, K, Q, S, hcomp, ⟨?_, ?_, ?_⟩, hS, ?_, ?_⟩
  · intro j
    simp [S, constantSeries]
  · intro j
    exact mem_annihilator A hs (S j) (hS j)
  · intro i j
    have hh := congrArg (fun z : Module.Dual ℝ E => z (b i)) (hQ j)
    change (b i).val (Q j) = b.dualBasis j (b i) at hh
    rw [← hSb i] at hh
    change pairing (S i) (Q j).val = b.dualBasis j (b i) at hh
    simpa only [Module.Basis.dualBasis_apply_self, eq_comm] using hh
  · intro i
    change (s (e i)).val - constantSeries ((s (e i)).val 1) = G i
    rw [hsg i]
    change G i - constantSeries (G i 1) = G i
    rw [hzero i]
    have hz : (constantSeries 0 : NCSeries X) = 0 := by funext w; simp [constantSeries]
    rw [hz, sub_zero]
  · exact mem_annihilator A hs

end Lax825748Proofs.CDAAmbient
