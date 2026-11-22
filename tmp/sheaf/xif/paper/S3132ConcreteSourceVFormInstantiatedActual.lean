import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.S3136ConcreteExample36NativeDataActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceCanonicalResidualActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceCanonicalResidualActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ConcreteExample36NativeDataActual

namespace LeanFormal.IUT.XiFPaper.S3132ConcreteSourceVFormInstantiatedActual

/-!
# Paper-route Theta side: concrete Example 3.6 instantiation of the V-form residual

**Component, not a paper object.**  Owner: hull.  Consumers: mainline
FINAL-STATUS/ledger; lattice index; Cor312EpsilonArithmeticComparisonV2
comparisonRegion.

Stage4 supplied the two concrete inputs (checker-verified, EXIT=0):

* `lgpConcreteExample36NativeData (M : LGPConcreteExample36NativeDataMissing l) :
  SourceNativeInitialThetaData.{0} l` — constructive passage from the exact
  concrete Example 3.6 data `M` (tuple + clauses A--F) to the native datum
  (S3136ConcreteExample36NativeDataActual 151784);
* `lgpNativeHaarFamily : (b) → Measure (qVFamTensorBlock T b)` = additive Haar
  with `IsAddHaarMeasure` instances and the measurable/Borel/proper/locally
  compact instances (S3136NativeHaarFamilyActual 151428);
  normalization is free for the canonical rooted readout.

This file instantiates hull's remaining Theta-half residual on the concrete
source side:

    MissingConcreteVFormCanonicalReadout T mu
      = (sourceVFormLogVolume = S3131CanonicalRootedHC T mu)

at `T := lgpConcreteExample36NativeData M`, `mu := lgpNativeHaarFamily T`, and
composes it with the CLOSED normalization factor (residual (2)) to obtain the
canonical raw/packaged source readout.  So the paper-route Theta side reduces to
the single exact data residual `LGPConcreteExample36NativeDataMissing` plus this
V-form/canonical identity (III Prop 3.9(i) p.115; Rem 3.9.5; Cor 3.12; IV
Prop 1.4(i)).
-/

variable {l : PrimeGeFive}
variable (M : LGPConcreteExample36NativeDataMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpConcreteExample36NativeData M)))]

/-- The concrete Example 3.6 native initial-Theta datum. -/
abbrev concreteExample36NativeData : SourceNativeInitialThetaData.{0} l :=
  lgpConcreteExample36NativeData M

/-- The concrete additive Haar family on its native qVFam tensor blocks. -/
abbrev concreteExample36Haar :
    (b : Bad (nativePlaceSelection (concreteExample36NativeData (l := l) M))) →
      Measure (qVFamTensorBlock (concreteExample36NativeData (l := l) M) b) :=
  lgpNativeHaarFamily (concreteExample36NativeData (l := l) M)

/-- **The instantiated paper-route Theta residual:** on the concrete Example 3.6
datum, the source V-form equals the canonical rooted `H_C` readout. -/
abbrev MissingConcreteExample36VFormCanonicalReadout : Prop :=
  MissingConcreteVFormCanonicalReadout
    (T := concreteExample36NativeData (l := l) M)
    (concreteExample36Haar (l := l) M)

/-- **Residual gives the canonical raw source reading** (factor (2) already
closed). -/
theorem concreteExample36RawLogVolume_eq_canonical
    (h : MissingConcreteExample36VFormCanonicalReadout (l := l) M) :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      S3131CanonicalRootedHC (l := l)
        (concreteExample36NativeData (l := l) M)
        (concreteExample36Haar (l := l) M) :=
  sourceRawLogVolume_eq_canonical_of_residual
    (T := concreteExample36NativeData (l := l) M)
    (mu := concreteExample36Haar (l := l) M) h

/-- **Residual gives the canonical packaged source readout.** -/
theorem concreteExample36CanonicalReadout
    (h : MissingConcreteExample36VFormCanonicalReadout (l := l) M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (l := l)
        (concreteExample36NativeData (l := l) M)
        (concreteExample36Haar (l := l) M) :=
  sourceCanonicalReadout_of_residual
    (T := concreteExample36NativeData (l := l) M)
    (mu := concreteExample36Haar (l := l) M) h

/-- **Paper-route Theta-side residual bundle (Prop form).**  The full remaining
content on the concrete Example 3.6 side is: a concrete native datum
(`SourceInitialThetaTuple` over the concrete Gaussian arithmetic + clauses A--F,
the exact data record `LGPConcreteExample36NativeDataMissing`) together with the
instantiated V-form/canonical identity for the additive Haar family. -/
def ConcreteExample36ThetaSideResidual : Prop :=
  ∃ (M : LGPConcreteExample36NativeDataMissing l)
    (f : Fintype (Bad (nativePlaceSelection (lgpConcreteExample36NativeData M)))),
    @MissingConcreteExample36VFormCanonicalReadout l M f

/-- The residual bundle yields the canonical packaged source readout (choose the
concrete data and apply the instantiated composition). -/
theorem concreteExample36CanonicalReadout_of_thetaSideResidual
    (h : ConcreteExample36ThetaSideResidual (l := l)) :
    ∃ (M : LGPConcreteExample36NativeDataMissing l)
      (f : Fintype (Bad (nativePlaceSelection (lgpConcreteExample36NativeData M)))),
      (Real.log sourceHullRealLogVolume =
        S3131CanonicalRootedHC (l := l)
          (lgpConcreteExample36NativeData M)
          (lgpNativeHaarFamily (lgpConcreteExample36NativeData M))) := by
  rcases h with ⟨M, f, hM⟩
  exact ⟨M, f, @concreteExample36CanonicalReadout l M f hM⟩

#check MissingConcreteExample36VFormCanonicalReadout
#check concreteExample36RawLogVolume_eq_canonical
#check concreteExample36CanonicalReadout
#check ConcreteExample36ThetaSideResidual

end LeanFormal.IUT.XiFPaper.S3132ConcreteSourceVFormInstantiatedActual

end