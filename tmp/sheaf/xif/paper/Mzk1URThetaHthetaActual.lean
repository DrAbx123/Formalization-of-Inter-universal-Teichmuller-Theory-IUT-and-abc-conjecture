/- U-R C2 theta side: honest composition of `htheta` (route §5.3 J1).

Route requirement: `actualThetaHullLogRoot T <= ucWeightedHpkt (nativeBadLocalWeight T) packetV`
(sophie's U-C input).  This file composes the two existing actual pieces:

* the actual root-hull scaling formula at `b`
  (`RootHullScalingFormulaAt T b : actualLocalHullLog T b = -thetaCoefficientContribution T b`,
  supplied by `BadPlaceRootHullScalingFormulaActual` from the exact half-generator supply
  datum `RootHullHalfScalingDataGap`);
* the actual weighted monotone sum (`Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt`).

The remaining inputs are explicit and honest:
(1) `hscale` : the root-hull half-scaling datum.  Its generator is an element of
    `CommonPrimeCompletion` of norm `p^(-c_norm/(2l))`, i.e. a `2l`-th root of the
    qVFamily q; `S342QVFamilyRootImpossibleActual` proves such a root does not exist in
    the completion, so this datum is exactly the missing root-extension -> tensor
    transport (not faked here).
(2) `hpacket` : the per-b numerical comparison of the packet value against the
    root-hull coefficient.  It needs the actual Kummer element `ϖ_b` (also a `2l`-th root)
    or the distinguished-slot relation `localNormOrder ϖ_b = c_norm_b/(2l)`; the tree has
    no actual `DistinguishedScalarData` instance (see `Mzk1ULPacketVActual`), so this is the
    same transport gap.

No surrogate, no zero-collapse, no `paperQFromM`-style definitional tautology. -/
import tmp.sheaf.xif.paper.Mzk1P6P5ThetaHullControl2
import tmp.sheaf.xif.paper.BadPlaceRootHullScalingFormulaActual
import tmp.sheaf.xif.paper.Mzk1URThetaPacketCarrierActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
open LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- **`htheta` from the root-hull scaling formula and the per-b packet
comparison** (route §5.3 J1): this is exactly sophie's
`thetaHullLog_le_ucHpkt` with the `hperB` input discharged through the actual root-hull
scaling formula. -/
theorem ur_htheta_of_scaling
    (hscale : ∀ b : Bad (nativePlaceSelection T),
      RootHullScalingFormulaAt (l := l) T b)
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hpacket : ∀ b, -thetaCoefficientContribution (l := l) T b ≤ packetV b) :
    actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (nativeBadLocalWeight T) packetV := by
  refine thetaHullLog_le_ucHpkt (l := l) T packetV ?_
  intro b
  unfold RootHullScalingFormulaAt at hscale
  rw [hscale b]
  exact hpacket b

/-- **`htheta` from the exact half-scaling gap datum**: the root-hull scaling
formulas are supplied by the explicit `RootHullHalfScalingDataGap` (half-generator
supply + hull equality), which is the exact missing root-extension transport input. -/
theorem ur_htheta_of_halfScalingData
    (G : ∀ b : Bad (nativePlaceSelection T),
      RootHullHalfScalingDataGap (l := l) T b)
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hpacket : ∀ b, -thetaCoefficientContribution (l := l) T b ≤ packetV b) :
    actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (nativeBadLocalWeight T) packetV :=
  ur_htheta_of_scaling (l := l) T
    (fun b => rootHullScalingFormulaAt_of_halfScalingData (l := l) T b (G b))
    packetV hpacket

/-- The root-hull coefficient as an actual `localNormOrder` expression: if a Kummer
element `ϖ` has `localNormOrder ϖ = c_norm/(2l)`, then the scaling formula's
right side is exactly `-localNormOrder ϖ * log p` (the normalized log-volume of
`ϖ O_hol`), i.e. the per-b packet comparison is the actual region-volume
comparison.  This makes the remaining input `hpacket` a pure numerical
`localNormOrder` comparison. -/
theorem ur_thetaCoeff_eq_neg_localNormOrder
    (b : Bad (nativePlaceSelection T))
    (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))
    (hvarpi : localNormOrder (qVFamTensorP T b) varpi =
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
        (2 * (l.value : ℝ))) :
    -thetaCoefficientContribution (l := l) T b =
      -localNormOrder (qVFamTensorP T b) varpi *
        Real.log (qVFamTensorP T b : ℝ) := by
  unfold thetaCoefficientContribution
  rw [hvarpi]
  ring

#print axioms ur_htheta_of_scaling
#print axioms ur_htheta_of_halfScalingData
#print axioms ur_thetaCoeff_eq_neg_localNormOrder

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual
end