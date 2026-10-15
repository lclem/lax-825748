import Lax825748.Series

/-!
---
title: Shuffle multiplication
type: definition and theorem
---
The coefficient of $w$ in the shuffle of $S$ and $T$ is the sum of
$S(w|I)T(w|I^c)$ over subsets of the positions of $w$. Repeated letters retain
their multiplicities. This product is associative and commutative, with unit
the series supported at the empty word. No concatenation product on series
is used here.
-/

noncomputable section

namespace Lax825748.Shuffle

open Series

def unshuffles {X : Type} : List X → List (List X × List X)
  | [] => [([], [])]
  | x :: w => (unshuffles w).flatMap fun p =>
      [(x :: p.1, p.2), (p.1, x :: p.2)]

noncomputable def shuffle {X : Type} (S T : NCSeries X) : NCSeries X :=
  fun w => ((unshuffles w.toList).map fun p =>
    S (FreeMonoid.ofList p.1) * T (FreeMonoid.ofList p.2)).sum

noncomputable def shuffleList {X : Type} : List (NCSeries X) → NCSeries X
  | [] => constantSeries 1
  | S :: l => shuffle S (shuffleList l)

noncomputable def shufflePow {X : Type} (S : NCSeries X) (n : ℕ) : NCSeries X :=
  shuffleList (List.replicate n S)

axiom commutative {X : Type} (S T : NCSeries X) : shuffle S T = shuffle T S

axiom associative {X : Type} (R S T : NCSeries X) :
  shuffle (shuffle R S) T = shuffle R (shuffle S T)

axiom unit {X : Type} (S : NCSeries X) : shuffle (constantSeries 1) S = S

end Lax825748.Shuffle
