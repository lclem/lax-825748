import Lax825748.FormalSeries

/-!
---
title: Formal changes of coordinates
type: definition
---
A formal change of coordinates is a real algebra automorphism of
$\mathbb R[[q_1,\ldots,q_d]]$ fixing the origin, continuous in both
directions for the formal topology. Its coordinate images and their inverse
images have zero constant term. Dimension zero is allowed.
-/

noncomputable section

namespace Lax825748.CoordinateChange

open FormalSeries

structure FormalChange (d : ℕ) where
  toAlgEquiv : StateSeries d ≃ₐ[ℝ] StateSeries d
  continuous_toFun : FormallyContinuous toAlgEquiv
  continuous_invFun : FormallyContinuous toAlgEquiv.symm
  origin : ∀ i, MvPowerSeries.constantCoeff (toAlgEquiv (MvPowerSeries.X i)) = 0
  inverse_origin : ∀ i,
    MvPowerSeries.constantCoeff (toAlgEquiv.symm (MvPowerSeries.X i)) = 0

end Lax825748.CoordinateChange
