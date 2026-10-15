import Lax825748Proofs.PBWIndependence

noncomputable section

namespace Lax825748Proofs.PBWSpanning

open Lax825748.Series Lax825748.LieRank Lax825748.PBW

variable {X : Type} {L : LieSubalgebra ℝ (NCPolynomial X)}

def evalWord {ι : Type} (b : Module.Basis ι ℝ L) (l : List ι) : NCPolynomial X :=
  (l.map fun i => (b i).val).prod

def sortedMonomial {ι : Type} [LinearOrder ι] (b : Module.Basis ι ℝ L)
    (l : OrderedWord ι) : NCPolynomial X := evalWord b l.val

def wordSpan {ι : Type} (b : Module.Basis ι ℝ L) (n : ℕ) :
    Submodule ℝ (NCPolynomial X) :=
  Submodule.span ℝ {P | ∃ l : List ι, l.length ≤ n ∧ P = evalWord b l}

theorem eval_mem {ι : Type} (b : Module.Basis ι ℝ L)
    (l : List ι) (n : ℕ) (h : l.length ≤ n) : evalWord b l ∈ wordSpan b n :=
  Submodule.subset_span ⟨l, h, rfl⟩

theorem wordSpan_mono {ι : Type} (b : Module.Basis ι ℝ L)
    {m n : ℕ} (h : m ≤ n) : wordSpan b m ≤ wordSpan b n := by
  apply Submodule.span_mono
  rintro P ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

theorem basis_left_mul {ι : Type} (b : Module.Basis ι ℝ L)
    (i : ι) {n : ℕ} {P : NCPolynomial X} (hP : P ∈ wordSpan b n) :
    (b i).val * P ∈ wordSpan b (n + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    simpa [evalWord] using eval_mem b (i :: l) (n + 1) (by simp; omega)
  | zero => simp
  | add P Q _ _ hP hQ => simpa only [mul_add] using (wordSpan b (n + 1)).add_mem hP hQ
  | smul a P _ hP =>
    simpa only [mul_smul_comm] using (wordSpan b (n + 1)).smul_mem a hP

theorem lie_left_mul {ι : Type} (b : Module.Basis ι ℝ L)
    (Q : L) {n : ℕ} {P : NCPolynomial X} (hP : P ∈ wordSpan b n) :
    Q.val * P ∈ wordSpan b (n + 1) := by
  have hQ : Q ∈ Submodule.span ℝ (Set.range b) := by rw [b.span_eq]; trivial
  induction hQ using Submodule.span_induction with
  | mem Q hQ => obtain ⟨i, rfl⟩ := hQ; exact basis_left_mul b i hP
  | zero => change (0 : NCPolynomial X) * P ∈ _; simp
  | add Q U _ _ hQ hU =>
    change (Q.val + U.val) * P ∈ _
    rw [add_mul]
    exact (wordSpan b (n + 1)).add_mem hQ hU
  | smul a Q _ hQ =>
    change (a • Q.val) * P ∈ _
    rw [smul_mul_assoc]
    exact (wordSpan b (n + 1)).smul_mem a hQ

theorem basis_right_mul {ι : Type} (b : Module.Basis ι ℝ L)
    (i : ι) {n : ℕ} {P : NCPolynomial X} (hP : P ∈ wordSpan b n) :
    P * (b i).val ∈ wordSpan b (n + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    simpa [evalWord, List.map_append, List.prod_append] using
      eval_mem b (l ++ [i]) (n + 1) (by simp; omega)
  | zero => simp
  | add P Q _ _ hP hQ => simpa only [add_mul] using (wordSpan b (n + 1)).add_mem hP hQ
  | smul a P _ hP =>
    simpa only [smul_mul_assoc] using (wordSpan b (n + 1)).smul_mem a hP

theorem lie_right_mul {ι : Type} (b : Module.Basis ι ℝ L)
    (Q : L) {n : ℕ} {P : NCPolynomial X} (hP : P ∈ wordSpan b n) :
    P * Q.val ∈ wordSpan b (n + 1) := by
  have hQ : Q ∈ Submodule.span ℝ (Set.range b) := by rw [b.span_eq]; trivial
  induction hQ using Submodule.span_induction with
  | mem Q hQ => obtain ⟨i, rfl⟩ := hQ; exact basis_right_mul b i hP
  | zero => change P * (0 : NCPolynomial X) ∈ _; simp
  | add Q U _ _ hQ hU =>
    change P * (Q.val + U.val) ∈ _
    rw [mul_add]
    exact (wordSpan b (n + 1)).add_mem hQ hU
  | smul a Q _ hQ =>
    change P * (a • Q.val) ∈ _
    rw [mul_smul_comm]
    exact (wordSpan b (n + 1)).smul_mem a hQ

theorem perm_difference {ι : Type} (b : Module.Basis ι ℝ L)
    {l m : List ι} (hp : l.Perm m) (n : ℕ) (hl : l.length ≤ n + 1) :
    evalWord b l - evalWord b m ∈ wordSpan b n := by
  induction hp generalizing n with
  | nil => simp
  | @cons a l m hp ih =>
    cases n with
    | zero =>
      have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
      have hm0 : m = [] := List.eq_nil_of_length_eq_zero (by rw [← hp.length_eq, hl0]; rfl)
      subst l; subst m
      simp
    | succ n =>
      have hx := basis_left_mul b a (ih n (by simp only [List.length_cons] at hl; omega))
      simpa only [evalWord, List.map_cons, List.prod_cons, mul_sub] using hx
  | swap a c l =>
    let Q : L := ⁅b c, b a⁆
    have hx := lie_left_mul b Q (eval_mem b l l.length le_rfl)
    have hdeg : l.length + 1 ≤ n := by simp only [List.length_cons] at hl; omega
    apply wordSpan_mono b hdeg
    convert hx using 1
    change (b c).val * ((b a).val * evalWord b l) -
      (b a).val * ((b c).val * evalWord b l) = Q.val * evalWord b l
    change _ = ((b c).val * (b a).val - (b a).val * (b c).val) * evalWord b l
    noncomm_ring
  | @trans l m k hlm hmk ih₁ ih₂ =>
    have h₁ := ih₁ n hl
    have h₂ := ih₂ n (by rw [← hlm.length_eq]; exact hl)
    have hh := (wordSpan b n).add_mem h₁ h₂
    convert hh using 1
    abel

theorem wordSpan_le_ordered {ι : Type} [LinearOrder ι]
    (b : Module.Basis ι ℝ L) (n : ℕ) :
    wordSpan b n ≤ Submodule.span ℝ (Set.range (sortedMonomial b)) := by
  induction n with
  | zero =>
    apply Submodule.span_le.mpr
    rintro P ⟨l, hl, rfl⟩
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst l
    exact Submodule.subset_span ⟨⟨[], by simp⟩, rfl⟩
  | succ n ih =>
    apply Submodule.span_le.mpr
    rintro P ⟨l, hl, rfl⟩
    let m : OrderedWord ι := ⟨l.mergeSort (· ≤ ·), List.pairwise_mergeSort' _ _⟩
    have hp : l.Perm m.val := (List.mergeSort_perm _ _).symm
    have hd := ih (perm_difference b hp n hl)
    have hm : evalWord b m.val ∈ Submodule.span ℝ (Set.range (sortedMonomial b)) :=
      Submodule.subset_span ⟨m, rfl⟩
    have hh := (Submodule.span ℝ (Set.range (sortedMonomial b))).add_mem hd hm
    rw [sub_add_cancel] at hh
    exact hh

theorem wordPolynomial_mem {X ι : Type} (b : Module.Basis ι ℝ (LiePolynomial X)) (w : Word X) :
    wordPolynomial w ∈ wordSpan b w.toList.length := by
  induction w using FreeMonoid.recOn with
  | one => exact eval_mem b [] 0 le_rfl
  | of_mul x w ih =>
    have hlie : letter x ∈ liePolynomials X := LieSubalgebra.subset_lieSpan (Set.mem_range_self x)
    have hh := lie_left_mul b (⟨letter x, hlie⟩ : LiePolynomial X) ih
    simpa only [Series.word_mul, letter, FreeMonoid.toList_of_mul, List.length_cons] using hh

theorem spanning {X ι : Type} [LinearOrder ι] (b : Module.Basis ι ℝ (LiePolynomial X)) :
    Submodule.span ℝ (Set.range (monomial b)) = ⊤ := by
  apply top_unique
  suffices h : ∀ P : NCPolynomial X, P ∈ Submodule.span ℝ (Set.range (monomial b)) by
    intro P _
    exact h P
  intro P
  induction P using MonoidAlgebra.induction_on with
  | of w => exact wordSpan_le_ordered b _ (wordPolynomial_mem b w)
  | add P Q hP hQ => exact Submodule.add_mem _ hP hQ
  | smul a P hP => exact Submodule.smul_mem _ a hP

end Lax825748Proofs.PBWSpanning
