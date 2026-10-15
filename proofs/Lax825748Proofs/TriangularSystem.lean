import Lax825748.FormalSeries
import Mathlib.Tactic

noncomputable section

namespace Lax825748Proofs.TriangularSystem

open Lax825748.Monomials
open scoped BigOperators

abbrev Index (d : ℕ) := Fin d →₀ ℕ

theorem degree_eq_total {d : ℕ} (I : Index d) : I.degree = totalDegree I := by
  change I.sum (fun _ n => n) = ∑ i, I i
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

def indices {d : ℕ} (n : ℕ) : Finset (Index d) :=
  (Finsupp.finite_of_degree_lt n).toFinset

@[simp] theorem mem_indices {d n : ℕ} {I : Index d} : I ∈ indices n ↔ I.degree < n := by
  simp [indices]

theorem indices_mono {d m n : ℕ} (h : m ≤ n) : (indices m : Finset (Index d)) ⊆ indices n := by
  intro I hi
  exact mem_indices.mpr (lt_of_lt_of_le (mem_indices.mp hi) h)

def solve {d : ℕ} (A : Index d → Index d → ℝ) (b : Index d → ℝ) (I : Index d) : ℝ :=
  (b I - ∑ J ∈ (indices I.degree).attach, solve A b J.val * A I J.val) / A I I
termination_by I.degree
decreasing_by exact mem_indices.mp J.property

theorem solve_recurrence {d : ℕ} (A : Index d → Index d → ℝ) (b : Index d → ℝ) (I : Index d) :
    solve A b I = (b I - ∑ J ∈ indices I.degree, solve A b J * A I J) / A I I := by
  conv_lhs => rw [solve]
  rw [Finset.sum_attach _ (fun J => solve A b J * A I J)]

def IsTriangular {d : ℕ} (A : Index d → Index d → ℝ) : Prop :=
  (∀ I J, I.degree = J.degree → I ≠ J → A I J = 0) ∧ ∀ I, A I I ≠ 0

theorem row_split {d : ℕ} (A : Index d → Index d → ℝ) (hA : IsTriangular A)
    (f : Index d → ℝ) (I : Index d) :
    (∑ J ∈ indices (I.degree + 1), f J * A I J) =
      (∑ J ∈ indices I.degree, f J * A I J) + f I * A I I := by
  classical
  rw [← Finset.sum_erase_add (indices (I.degree + 1)) (fun J => f J * A I J)
    (mem_indices.mpr (Nat.lt_succ_self _))]
  congr 1
  symm
  apply Finset.sum_subset
  · intro J hJ
    apply Finset.mem_erase.mpr
    refine ⟨?_, indices_mono (Nat.le_succ _) hJ⟩
    intro he
    subst J
    exact (Nat.lt_irrefl I.degree) (mem_indices.mp hJ)
  · intro J hJ hnot
    obtain ⟨hJI, hJ⟩ := Finset.mem_erase.mp hJ
    have hd : J.degree = I.degree := by
      have hlt := mem_indices.mp hJ
      have hn : ¬ J.degree < I.degree := fun h => hnot (mem_indices.mpr h)
      omega
    rw [hA.1 I J hd.symm (Ne.symm hJI), mul_zero]

theorem solve_rows {d : ℕ} (A : Index d → Index d → ℝ) (hA : IsTriangular A)
    (b : Index d → ℝ) (I : Index d) :
    (∑ J ∈ indices (I.degree + 1), solve A b J * A I J) = b I := by
  rw [row_split A hA, solve_recurrence, div_mul_cancel₀ _ (hA.2 I)]
  ring

theorem solution_recurrence {d : ℕ} (A : Index d → Index d → ℝ) (hA : IsTriangular A)
    (b f : Index d → ℝ)
    (hf : ∀ I, (∑ J ∈ indices (I.degree + 1), f J * A I J) = b I) (I : Index d) :
    f I = (b I - ∑ J ∈ indices I.degree, f J * A I J) / A I I := by
  apply (eq_div_iff (hA.2 I)).mpr
  have hh := hf I
  rw [row_split A hA] at hh
  linarith

theorem solution_unique {d : ℕ} (A : Index d → Index d → ℝ) (hA : IsTriangular A)
    (b f g : Index d → ℝ)
    (hf : ∀ I, (∑ J ∈ indices (I.degree + 1), f J * A I J) = b I)
    (hg : ∀ I, (∑ J ∈ indices (I.degree + 1), g J * A I J) = b I) : f = g := by
  have he : ∀ n, ∀ I : Index d, I.degree = n → f I = g I := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I hI
      rw [solution_recurrence A hA b f hf, solution_recurrence A hA b g hg]
      congr 2
      apply Finset.sum_congr rfl
      intro J hJ
      rw [ih J.degree (by have := mem_indices.mp hJ; omega) J rfl]
  exact funext fun I => he I.degree I rfl

end Lax825748Proofs.TriangularSystem
