import tmp.sheaf.xif.paper.Mzk1P3DictQPacketSignedActual
import Mathlib.Tactic

/-! # CONDITIONAL/GREEN: paper Q source builder from actual qPacket -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictQSourceBuilderActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictQPacketSignedActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Paper Q source with the actual qPacket signed log. -/
structure PaperQSource where
  logQ : Real
  paperQ : Real
  logQ_eq : logQ = qPacketSignedLogQ (l := l) T
  paperQ_eq : paperQ = ((l.value + 1) / 24) * logQ

/-- Builder: use the actual qPacket reading. -/
def paperQSourceOfQPacket : PaperQSource (l := l) T where
  logQ := qPacketSignedLogQ (l := l) T
  paperQ := ((l.value + 1) / 24) * qPacketSignedLogQ (l := l) T
  logQ_eq := rfl
  paperQ_eq := rfl

/-- The builder's logQ is minus the unweighted base-q total. -/
theorem paperQSourceOfQPacket_logQ :
    (paperQSourceOfQPacket (l := l) T).logQ = -baseQTotalLogMagnitude T :=
  qPacketSignedLogQ_eq_neg_baseQTotal (l := l) T

#check PaperQSource
#check paperQSourceOfQPacket
#check paperQSourceOfQPacket_logQ
end LeanFormal.IUT.XiFPaper.Mzk1P3DictQSourceBuilderActual
end
