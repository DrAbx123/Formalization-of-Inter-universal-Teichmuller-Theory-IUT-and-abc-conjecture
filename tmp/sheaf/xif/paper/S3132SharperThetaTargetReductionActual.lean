import tmp.sheaf.xif.paper.S3132ThetaNormalizationFactorActual
import tmp.sheaf.xif.paper.S3132CanonicalRootedThetaTargetActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3132CanonicalRootedThetaTargetActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S3131HullActualReadout
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type}
variable {I2 : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I2)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-!
# task-41: reduction of the sharper Theta target to two field-level residuals

**Component, not a paper object.**  Owner: hull.  Consumer: the normalization
residual `MissingThetaLogNormalization` (task-38) and shehdd's canonical wiring.

The sharper paper-faithful target (task-41) is
`thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu`.  Using the exact
decomposition proved in `S3132ThetaNormalizationFactorActual`

    thetaPilotHullLogVolumeReal C3 = V(actual paper hull) + thetaNormalizationFactor C3,

this module reduces the target to **two independent field-level residuals**:

1. `MissingVFormCanonicalIdentification`: the actual degree-normalized V-form of
   the actual paper hull equals the canonical rooted V-form readout
   `S3134CanonicalRootedHC T mu` (paper normalization / rooted readout identity;
   IUT III, Proposition 3.9, (i), p. 115; Corollary 3.12, corpus:10324-10353);
2. `thetaNormalizationFactor C3 = 0`: the exact normalization factor of the raw
   Haar reading vanishes (equivalently the raw C3 reading is already the V-form
   of the actual paper hull; explicit value in
   `S3132ThetaNormalizationFactorActual.thetaNormalizationFactor_eq`).

Given (1), the target is *equivalent* to (2) (theorem
`canonicalTarget_iff_factor_zero_of_VForm`); given both, the target follows
(theorem `MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm`).
The transport residual `MissingC3PacketUniformComparison` is not used.
-/

/-- **Residual (1):** the actual V-form of the actual paper hull equals the
canonical rooted V-form readout.  Exact missing, owner hull/mainline. -/
structure MissingVFormCanonicalIdentification : Prop where
  vform_eq_canonical :
    c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) =
      S3134CanonicalRootedHC T mu

/-- **Reduction:** the sharper target follows from the V-form/canonical
identification and vanishing of the exact normalization factor. -/
theorem MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm
    (hfac : thetaNormalizationFactor C3 = 0)
    (hV : MissingVFormCanonicalIdentification C3 T mu) :
    MissingCanonicalRootedThetaReadout I C3 T mu :=
  ⟨by
    rw [thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor, hfac, add_zero]
    exact hV.vform_eq_canonical⟩

/-- **Equivalence form:** once the V-form/canonical identification holds, the
sharper target is equivalent to the vanishing of the exact normalization
factor. -/
theorem canonicalTarget_iff_factor_zero_of_VForm
    (hV : MissingVFormCanonicalIdentification C3 T mu) :
    thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu ↔
      thetaNormalizationFactor C3 = 0 := by
  constructor
  · intro h
    have hraw := thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor C3
    rw [h] at hraw
    rw [← hV.vform_eq_canonical] at hraw
    have h2 : c3NormalizedLogVolume C3
          (actualHolomorphicHull C3 (actualUnitRegion C3)) + 0 =
        c3NormalizedLogVolume C3
          (actualHolomorphicHull C3 (actualUnitRegion C3)) + thetaNormalizationFactor C3 :=
      (add_zero (c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)))).trans hraw
    exact (add_left_cancel h2).symm
  · intro hfac
    rw [thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor, hfac, add_zero]
    exact hV.vform_eq_canonical

/-- The shehdd canonical alias is definitionally the mainline canonical rooted
V-form readout `S3131CanonicalRootedHC`. -/
theorem S3134CanonicalRootedHC_eq_S3131CanonicalRootedHC :
    S3134CanonicalRootedHC T mu = S3131CanonicalRootedHC T mu :=
  rfl

/-- **Exact-factor form of the sharper target (no V-form assumption needed).**  The
canonical target is equivalent to the exact normalization factor taking the
explicit value `S3134CanonicalRootedHC T mu - V(actual paper hull)`
(`S3134CanonicalRootedHC = S3131CanonicalRootedHC` definitionally; see
`S3132CanonicalVFormValueActual`). -/
theorem canonicalTarget_iff_factor_eq :
    thetaPilotHullLogVolumeReal C3 = S3134CanonicalRootedHC T mu ↔
      thetaNormalizationFactor C3 =
        S3134CanonicalRootedHC T mu -
          c3NormalizedLogVolume C3
            (actualHolomorphicHull C3 (actualUnitRegion C3)) := by
  rw [thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor]
  constructor
  · intro h
    have h2 : thetaNormalizationFactor C3 =
        S3134CanonicalRootedHC T mu -
          c3NormalizedLogVolume C3
            (actualHolomorphicHull C3 (actualUnitRegion C3)) := by
      rw [← h]; ring
    exact h2
  · intro h
    rw [h]; ring

#check MissingVFormCanonicalIdentification
#check MissingCanonicalRootedThetaReadout_of_factor_zero_and_VForm
#check canonicalTarget_iff_factor_zero_of_VForm
#check canonicalTarget_iff_factor_eq

end LeanFormal.IUT.XiFPaper.S3132SharperThetaTargetReductionActual

end