import tmp.sheaf.xif.paper.S1939RootPacketDeterminantActual
import tmp.sheaf.xif.paper.S1948HullScaleBoundActual

noncomputable section

namespace S1948Consumer

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1939RootPacketDeterminantActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1948HullScaleBoundActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]

example (h : S1948FirstMissing T) : ¬ s1939HullScaleBound T :=
  s1948_precise_first_missing T h

example (h : S1948FirstMissing T) : s1939BadLog T ≤ -Real.log 2 :=
  s1948_badLog_le_neg_log_two T h

example : S1948HullScaleBound T ↔
    1 - s1939MeanSquare l / (lStar l.value : Real) ^ 2 ≤ s1915ClosedForm T :=
  s1948HullScaleBound_iff_closedForm_lower T

end S1948Consumer
