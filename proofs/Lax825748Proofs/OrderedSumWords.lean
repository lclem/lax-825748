import Mathlib.Data.List.Sort
import Mathlib.Data.Sum.Order

namespace Lax825748Proofs.OrderedSumWords

def leftEntry {α β : Type} (a : α ⊕ₗ β) : Option α :=
  match ofLex a with
  | Sum.inl i => some i
  | Sum.inr _ => none

def rightEntry {α β : Type} (a : α ⊕ₗ β) : Option β :=
  match ofLex a with
  | Sum.inl _ => none
  | Sum.inr j => some j

def leftPart {α β : Type} (l : List (α ⊕ₗ β)) : List α := l.filterMap leftEntry
def rightPart {α β : Type} (l : List (α ⊕ₗ β)) : List β := l.filterMap rightEntry

@[simp] theorem leftPart_left {α β : Type} (l : List α) :
    leftPart (l.map fun i => toLex (Sum.inl i : α ⊕ β)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [leftPart, List.filterMap_cons, leftEntry] using ih

@[simp] theorem rightPart_left {α β : Type} (l : List α) :
    rightPart (l.map fun i => toLex (Sum.inl i : α ⊕ β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [rightPart, List.filterMap_cons, rightEntry]

@[simp] theorem rightPart_right {α β : Type} (l : List β) :
    rightPart (l.map fun j => toLex (Sum.inr j : α ⊕ β)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [rightPart, List.filterMap_cons, rightEntry] using ih

@[simp] theorem rightPart_append {α β : Type} (l m : List (α ⊕ₗ β)) :
    rightPart (l ++ m) = rightPart l ++ rightPart m := by simp [rightPart]

theorem left_ordered {α β : Type} [LinearOrder α] [LinearOrder β]
    (l : List (α ⊕ₗ β)) (hl : l.Pairwise (· ≤ ·)) : (leftPart l).Pairwise (· ≤ ·) := by
  apply List.Pairwise.filterMap leftEntry ?_ hl
  intro a b hab i hi j hj
  cases ea : ofLex a with
  | inr k => simp [leftEntry, ea] at hi
  | inl k =>
    have ha : a = toLex (Sum.inl k) := by rw [← ea]; simp
    subst a
    cases eb : ofLex b with
    | inr k => simp [leftEntry, eb] at hj
    | inl u =>
      have hb : b = toLex (Sum.inl u) := by rw [← eb]; simp
      subst b
      simp [leftEntry] at hi hj
      subst i; subst j
      exact Sum.Lex.inl_le_inl_iff.mp hab

theorem right_ordered {α β : Type} [LinearOrder α] [LinearOrder β]
    (l : List (α ⊕ₗ β)) (hl : l.Pairwise (· ≤ ·)) : (rightPart l).Pairwise (· ≤ ·) := by
  apply List.Pairwise.filterMap rightEntry ?_ hl
  intro a b hab i hi j hj
  cases ea : ofLex a with
  | inl k => simp [rightEntry, ea] at hi
  | inr k =>
    have ha : a = toLex (Sum.inr k) := by rw [← ea]; simp
    subst a
    cases eb : ofLex b with
    | inl k => simp [rightEntry, eb] at hj
    | inr u =>
      have hb : b = toLex (Sum.inr u) := by rw [← eb]; simp
      subst b
      simp [rightEntry] at hi hj
      subst i; subst j
      exact Sum.Lex.inr_le_inr_iff.mp hab

theorem split_ordered {α β : Type} [LinearOrder α] [LinearOrder β]
    (l : List (α ⊕ₗ β)) (hl : l.Pairwise (· ≤ ·)) :
    l = (leftPart l).map (fun i => toLex (Sum.inl i)) ++
      (rightPart l).map (fun j => toLex (Sum.inr j)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hl
    cases ea : ofLex a with
    | inl i =>
      have he : a = toLex (Sum.inl i) := by rw [← ea]; simp
      subst a
      simpa [leftPart, rightPart, List.filterMap_cons, leftEntry, rightEntry] using
        congrArg (List.cons (toLex (Sum.inl i))) (ih ht)
    | inr j =>
      have he : a = toLex (Sum.inr j) := by rw [← ea]; simp
      subst a
      have hleft : leftPart l = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro b hb
        cases eb : ofLex b with
        | inl i =>
          have he : b = toLex (Sum.inl i) := by rw [← eb]; simp
          subst b
          exact (Sum.Lex.not_inr_le_inl (ha _ hb)).elim
        | inr k => simp [leftEntry, eb]
      have htail := ih ht
      rw [hleft, List.map_nil, List.nil_append] at htail
      change toLex (Sum.inr j) :: l =
        (leftPart l).map (fun i => toLex (Sum.inl i)) ++
          toLex (Sum.inr j) :: (rightPart l).map (fun k => toLex (Sum.inr k))
      rw [hleft]
      exact congrArg (List.cons (toLex (Sum.inr j))) htail

theorem ordered_append {α β : Type} [LinearOrder α] [LinearOrder β]
    (l : List α) (m : List β) (hl : l.Pairwise (· ≤ ·)) (hm : m.Pairwise (· ≤ ·)) :
    ((l.map fun i => toLex (Sum.inl i)) ++ (m.map fun j => toLex (Sum.inr j))).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact List.Pairwise.map _ (fun _ _ h => Sum.Lex.inl_le_inl_iff.mpr h) hl
  · exact List.Pairwise.map _ (fun _ _ h => Sum.Lex.inr_le_inr_iff.mpr h) hm
  · rintro a ha b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact Sum.Lex.inl_le_inr i j

end Lax825748Proofs.OrderedSumWords
