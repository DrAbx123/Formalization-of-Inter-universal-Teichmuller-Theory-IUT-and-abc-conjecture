import tmp.sheaf.xif.paper.S3136ModelClauseWitnessAdapterActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceCanonicalResidualActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

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
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelClauseWitnessAdapterActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseResidualActual

/-! # Paper-route Theta side: V-form residual on stage4's concrete clause data

Consumes stage4's `LGPConcreteClauseData` (concrete-arithmetic clause data from a
SourceClauseConstructionWitness, S3136ModelClauseWitnessAdapterActual) and the
constructive native datum `lgpConcreteClauseData_toNativeData`, together with the
concrete additive Haar family.  The single remaining identity is the V-form /
canonical rooted readout equality; the normalization factor residual is CLOSED
(S3132ConcreteSourceNormalizationClosureActual).  Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPConcreteClauseData l)
variable [Fintype (Bad (nativePlaceSelection (lgpConcreteClauseData_toNativeData M)))]

/-- The concrete native datum from the clause data. -/
abbrev clauseNativeData : SourceNativeInitialThetaData.{0} l :=
  lgpConcreteClauseData_toNativeData M

/-- The concrete additive Haar family on its native qVFam blocks. -/
abbrev clauseHaar :
    (b : Bad (nativePlaceSelection (clauseNativeData (l := l) M))) →
      Measure (qVFamTensorBlock (clauseNativeData (l := l) M) b) :=
  lgpNativeHaarFamily (clauseNativeData (l := l) M)

/-- **The clause-data Theta-side residual:** source V-form = canonical rooted
readout on the stage4 clause datum with the concrete Haar family. -/
abbrev ClauseSideVFormResidual : Prop :=
  MissingConcreteVFormCanonicalReadout
    (T := clauseNativeData (l := l) M) (clauseHaar (l := l) M)

/-- The residual is one real identity. -/
theorem clauseSideVFormResidual_iff :
    ClauseSideVFormResidual (l := l) M ↔
      (sourceVFormLogVolume =
        S3131CanonicalRootedHC (l := l)
          (clauseNativeData (l := l) M) (clauseHaar (l := l) M)) := by
  constructor
  · intro h; exact h.vform_eq_canonical
  · intro h; exact ⟨h⟩

/-- **Canonical raw source reading from the clause residual.** -/
theorem clauseRawLogVolume_eq_canonical
    (h : ClauseSideVFormResidual (l := l) M) :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      S3131CanonicalRootedHC (l := l)
        (clauseNativeData (l := l) M) (clauseHaar (l := l) M) :=
  sourceRawLogVolume_eq_canonical_of_residual
    (T := clauseNativeData (l := l) M) (mu := clauseHaar (l := l) M) h

/-- **Canonical packaged source readout from the clause residual.** -/
theorem clauseCanonicalReadout
    (h : ClauseSideVFormResidual (l := l) M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (l := l)
        (clauseNativeData (l := l) M) (clauseHaar (l := l) M) :=
  sourceCanonicalReadout_of_residual
    (T := clauseNativeData (l := l) M) (mu := clauseHaar (l := l) M) h

#check ClauseSideVFormResidual
#check clauseSideVFormResidual_iff
#check clauseRawLogVolume_eq_canonical
#check clauseCanonicalReadout

end LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseResidualActual
end
