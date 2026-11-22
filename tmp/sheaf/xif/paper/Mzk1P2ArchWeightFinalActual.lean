import tmp.sheaf.xif.paper.Mzk1P2ArchLogSourceActual
/-! P2 arch weight final status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2ArchWeightFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2ArchLogSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
def archWeightFinalRows : List String :=
  [ "archMetric = -CK * archLog", "exact iff archMetric = CK*p2R13Exact <-> archLog = p2WeightedDetLog",
    "source identification missing" ]
theorem archWeightFinalRows_length : archWeightFinalRows.length = 3 := rfl

/-- Exact arch source criterion, re-exported. -/
theorem archWeightFinal_iff {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (f : (T.arithmetic.K)ˣ) :
    archDetMetricWeight (F := T.arithmetic.K) f =
        archCK (T.arithmetic.K) * p2R13Exact T ↔
      archimedeanLogNorm (F := T.arithmetic.K) (f : T.arithmetic.K) =
        p2WeightedDetLog T :=
  p2ArchMetric_eq_archCK_mul_p2R13Exact_iff T f
end LeanFormal.IUT.XiFPaper.Mzk1P2ArchWeightFinalActual
end
