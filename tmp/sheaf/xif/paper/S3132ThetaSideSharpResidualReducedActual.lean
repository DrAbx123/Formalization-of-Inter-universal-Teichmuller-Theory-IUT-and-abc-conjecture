import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualActual
import tmp.sheaf.xif.paper.S3132RootedScalingDataTrivialActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual

/-!
# Paper-route Theta side: sharp residual reduced to the weighted rooted identity

By S3132RootedScalingDataTrivialActual the rooted scaling decomposition (R1) is
content-free (scalar = exp of the rooted log-volume), so the sharp residual
ThetaSideSharpResidual is EQUIVALENT to the weighted rooted identity (R2):
  sourceVFormLogVolume = sum_b nativeBadLocalWeight b * rootThetaHullLog_b.
R2 is the paper log-volume dictionary computation (III Prop 3.9(i); Rem 3.9.5(i)),
not an independent hard input.  Component, not a paper object; owner hull.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- (R2) on the concrete model data: the weighted rooted log-volume identity. -/
abbrev ModelWeightedRootedIdentity : Prop :=
  WeightedRootedIdentity (T := lgpModelNativeData M)
    (fun b => lgpNativeHaarFamily (lgpModelNativeData M) b)

/-- The sharp residual is EXACTLY the weighted rooted identity (R2). -/
theorem sharpResidual_iff_weightedIdentity :
    ThetaSideSharpResidual M ↔ ModelWeightedRootedIdentity M := by
  constructor
  · intro h
    unfold ModelWeightedRootedIdentity WeightedRootedIdentity
    rw [h.vform_eq_canonical]
    rw [canonicalReadout_eq_weightedRootedLog (T := lgpModelNativeData M)
      (mu := fun b => lgpNativeHaarFamily (lgpModelNativeData M) b)]
  · intro h
    exact ⟨vformCanonical_of_weightedIdentity (T := lgpModelNativeData M)
      (mu := fun b => lgpNativeHaarFamily (lgpModelNativeData M) b) h⟩

/-- The weighted identity yields the canonical packaged source readout. -/
theorem weightedIdentity_canonicalReadout
    (h : ModelWeightedRootedIdentity M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (lgpModelNativeData M)
        (fun b => lgpNativeHaarFamily (lgpModelNativeData M) b) :=
  modelCanonicalReadout M ((sharpResidual_iff_weightedIdentity M).mpr h)

#check ModelWeightedRootedIdentity
#check sharpResidual_iff_weightedIdentity
#check weightedIdentity_canonicalReadout

end LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual
end