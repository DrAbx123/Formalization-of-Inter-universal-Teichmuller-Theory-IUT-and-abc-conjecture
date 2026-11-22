import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.S3136ConcreteExample36NativeDataActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceNormalizationClosureActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceCanonicalResidualActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1200000

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideMilestoneRecordActual

/-! # Paper-route Theta side: milestone record (dependency order + residual ids)

Structured record of the paper-route Theta-side milestone after integrating
stage4's concrete prerequisites.  Machine-checkable declarations only; the
record itself is data (strings/lists) for the registry/ledger, not an argument.

Dependency order (all links checker-verified or proved in hull files):
1. exact concrete data residual: LGPConcreteExample36NativeDataMissing l
   (SourceInitialThetaTuple over concreteGaussianInitialThetaArithmeticData l +
   clauses A--F of IUT I Def 3.1) -- stage4 S3136ConcreteExample36NativeDataActual;
2. constructive passage to the native datum:
   lgpConcreteExample36NativeData M : SourceNativeInitialThetaData l;
3. concrete additive Haar family: lgpNativeHaarFamily T
   : (b) -> Measure (qVFamTensorBlock T b), IsAddHaarMeasure -- stage4
   S3136NativeHaarFamilyActual; normalization free for the V-form readout;
4. normalization factor residual CLOSED on the concrete source model:
   S3132ConcreteSourceNormalizationClosureActual (factor = 0 via unit-reference
   mass one);
5. single remaining identity: MissingConcreteVFormCanonicalReadout T mu
   (sourceVFormLogVolume = S3131CanonicalRootedHC T mu) --
   S3132ConcreteSourceCanonicalResidualActual (CITABLE);
6. composition: S3132ConcreteSourceVFormInstantiatedActual
   (concreteExample36RawLogVolume_eq_canonical,
   concreteExample36CanonicalReadout, ConcreteExample36ThetaSideResidual).
-/

/-- Structured milestone record for the paper-route Theta side. -/
structure ThetaSideMilestoneRecord where
  id : String
  dataResidual : String
  haarFamily : String
  normalizationClosure : String
  vformResidual : String
  composition : String
  dependencyOrder : List String

/-- The actual milestone record (paper-route Theta side). -/
def thetaSideMilestoneRecord : ThetaSideMilestoneRecord :=
  { id := "XiF.ThetaSide.concrete-example36-milestone"
    dataResidual := "LGPConcreteExample36NativeDataMissing"
    haarFamily := "lgpNativeHaarFamily"
    normalizationClosure := "sourceThetaNormalizationFactor_eq_zero"
    vformResidual := "MissingConcreteVFormCanonicalReadout"
    composition := "concreteExample36CanonicalReadout"
    dependencyOrder :=
      ["data-residual", "native-datum-construction", "haar-family",
       "normalization-closure", "vform-canonical-identity",
       "canonical-readout-composition"] }

/-- The record's id is stable. -/
theorem thetaSideMilestoneRecord_id :
    thetaSideMilestoneRecord.id = "XiF.ThetaSide.concrete-example36-milestone" :=
  rfl

#check ThetaSideMilestoneRecord
#check thetaSideMilestoneRecord
#check thetaSideMilestoneRecord_id

end LeanFormal.IUT.XiFPaper.S3132ThetaSideMilestoneRecordActual
end
