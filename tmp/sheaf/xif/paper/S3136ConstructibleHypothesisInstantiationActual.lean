import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Stage-4 host: constructible pieces instantiating (c)-side hypotheses

Source anchors: IUT IV, Theorem 1.10 hypotheses p.1255-1292 (initial Theta-data;
Theta-pilot data); IUT IV, Prop 1.4 (log-volumes); IUT III, Prop 3.2, (ii)
(tensor log-shell regions); IUT III, Prop 3.9, (i) (normalized log-volumes).

CONSUMER: mainline's IUT IV skeleton hypothesis slots. This file collects the
constructible witness terms: the additive Haar family (as an existential witness),
the model Theta packet (as the Theta-values witness), the theta tensor region
family, and the conditional native initial-Theta datum, each with the exact
theorem witnessing that the corresponding hypothesis is instantiated.

LABEL: hypothesis instantiation witnesses (class A). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ConstructibleHypothesisInstantiationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open MeasureTheory

variable {l : PrimeGeFive}

/-- The native additive Haar family exists as an actual witnesses family. -/
theorem lgpNativeHaarFamily_provides_additiveHaar
    (T : SourceNativeInitialThetaData.{0} l) :
    ∃ mu : (b : Bad (nativePlaceSelection T)) → Measure (qVFamTensorBlock T b),
      ∀ b, Measure.IsAddHaarMeasure (mu b) :=
  ⟨lgpNativeHaarFamily T, lgpNativeHaarFamily_isAddHaar T⟩

/-- The model Theta packet provides the Theta-value hypothesis data. -/
theorem lgpModelThetaPacket_provides_thetaValues (l : PrimeGeFive) :
    ∃ packet : FiniteThetaPacket l, packet.q = gaussianFiveThetaQ :=
  ⟨lgpModelThetaPacket l, lgpModelThetaPacket_q l⟩

/-- The theta tensor region family at a fixed label (region hypothesis data). -/
def lgpThetaRegionFamily (T : SourceNativeInitialThetaData.{0} l)
    (j : SignedLabel l.value) :
    (b : Bad (nativePlaceSelection T)) → Set (qVFamTensorBlock T b) :=
  fun b => qVFamThetaTensorRegion T b j

/-- The conditional native initial-Theta datum provides the IUT I Def 3.1
hypothesis (its arithmetic is the concrete Gaussian arithmetic). -/
theorem lgpModelSourceClause_provides_nativeDatum
    (M : LGPModelSourceClauseMissing l) :
    (lgpModelNativeData M).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  lgpModelNativeData_arithmetic M

#check lgpNativeHaarFamily_provides_additiveHaar
#check lgpModelThetaPacket_provides_thetaValues
#check lgpThetaRegionFamily
#check lgpModelSourceClause_provides_nativeDatum

end LeanFormal.IUT.XiFPaper.S3136ConstructibleHypothesisInstantiationActual
end