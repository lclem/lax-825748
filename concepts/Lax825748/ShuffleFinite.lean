import Lax825748.ShuffleIdentities
import Mathlib.LinearAlgebra.Span.Defs

/-!
---
title: Shuffle-finite series
type: definition
---
A series is shuffle finite if it belongs to a finitely generated unital
shuffle subalgebra stable under prefix derivatives. Finite generation is
expressed by spanning all shuffle monomials in a finite family of series.
Only finite linear combinations enter this algebra; its formal completion
is a separate construction.
-/

noncomputable section

namespace Lax825748.ShuffleFinite

open Series Shuffle ShuffleIdentities

structure ShuffleSubalgebra (X : Type) where
  toSubmodule : Submodule ℝ (NCSeries X)
  one_mem : constantSeries 1 ∈ toSubmodule
  shuffle_mem : ∀ S T, S ∈ toSubmodule → T ∈ toSubmodule → shuffle S T ∈ toSubmodule

def FinitelyGenerated {X : Type} (A : ShuffleSubalgebra X) : Prop :=
  ∃ (n : ℕ) (S : Fin n → NCSeries X),
    A.toSubmodule = Submodule.span ℝ (Set.range fun I : Fin n → ℕ => shuffleMonomial S I)

def DerivativeStable {X : Type} (A : ShuffleSubalgebra X) : Prop :=
  ∀ (x : X) (T : NCSeries X), T ∈ A.toSubmodule →
    rightResidual T (letter x) ∈ A.toSubmodule

def IsShuffleFinite {X : Type} (f : NCSeries X) : Prop :=
  ∃ A : ShuffleSubalgebra X, FinitelyGenerated A ∧ DerivativeStable A ∧ f ∈ A.toSubmodule

end Lax825748.ShuffleFinite
