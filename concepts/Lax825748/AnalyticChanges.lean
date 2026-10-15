import Lax825748.ConvergentSeries
import Lax825748.CoordinateChange

/-!
---
title: Analytic changes of coordinates
type: theorem
---
An analytic change of coordinates is a formally continuous real algebra
automorphism fixing the origin whose coordinate images, in both directions,
are convergent power series.

The analytic inverse function theorem implies that a formal change of
coordinates with convergent coordinate images has convergent inverse images.
This is the implicit function theorem used in part b) of the paper.
-/

noncomputable section

namespace Lax825748.AnalyticChanges

open Lax825748.FormalSeries Lax825748.CoordinateChange ConvergentSeries

structure AnalyticChange (d : ℕ) extends FormalChange d where
  convergent_toFun : ∀ i, Convergent (toAlgEquiv (MvPowerSeries.X i))
  convergent_invFun : ∀ i, Convergent (toAlgEquiv.symm (MvPowerSeries.X i))

axiom inverse_convergent {d : ℕ} (φ : FormalChange d)
    (hφ : ∀ i, Convergent (φ.toAlgEquiv (MvPowerSeries.X i))) :
  ∀ i, Convergent (φ.toAlgEquiv.symm (MvPowerSeries.X i))

end Lax825748.AnalyticChanges
