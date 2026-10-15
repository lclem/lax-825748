import Lax825748.FormalSeries

/-!
---
title: Formal differential representations
type: definition
---
A formal differential representation of dimension $d$ consists of one
formal vector field for each letter and an arbitrary formal output series $h$.
The operators act on the right: the word $xy$ applies the field for $x$
first and then the field for $y$. Its generated coefficient at $w$ is
the constant term of $h\mu w$.

Specifying the fields is equivalent to specifying the monoid homomorphism
$\mu$. All state series and vector-field coefficients are formal.
-/

noncomputable section

namespace Lax825748.DifferentialRepresentation

open Series FormalSeries

structure Representation (X : Type) (d : ℕ) where
  fields : X → VectorField d
  output : StateSeries d

noncomputable def act {X : Type} {d : ℕ} (R : Representation X d)
    (f : StateSeries d) (w : Word X) : StateSeries d :=
  w.toList.foldl (fun k x => applyVectorField (R.fields x) k) f

noncomputable def generatingSeries {X : Type} {d : ℕ}
    (R : Representation X d) : NCSeries X :=
  fun w => MvPowerSeries.constantCoeff (act R R.output w)

def Represents {X : Type} {d : ℕ} (R : Representation X d)
    (g : NCSeries X) : Prop := generatingSeries R = g

def DifferentiallyProduced {X : Type} (g : NCSeries X) : Prop :=
  ∃ d, ∃ R : Representation X d, Represents R g

end Lax825748.DifferentialRepresentation
