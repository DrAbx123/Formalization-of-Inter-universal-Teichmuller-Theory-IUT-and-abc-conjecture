import tmp.sheaf.xif.paper.Mzk1P3NetGainCorrectionsActual
import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
/-! P3 (R3.7) x P2: explicit net quantity built from P2 R1.2/R1.3/det data. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NetGainP2Actual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainCorrectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- P2 corrections: the R1.3 mass difference `p2R13Exact` enters the reference term. -/
def p2NetCorrections : NetCorrections :=
  { normRatio := 0, degreeWeight := 0, referenceMassDiff := p2R13Exact T }
theorem p2NetCorrections_total :
    (p2NetCorrections T).total = p2R13Exact T := by
  unfold p2NetCorrections NetCorrections.total
  ring
/-- Explicit net quantity on the actual P2 data. -/
theorem netQuantity_p2_eq (G h : ℝ) :
    netQuantity G h (p2NetCorrections T).total = G - Real.log h + p2R13Exact T := by
  rw [p2NetCorrections_total]
  unfold netQuantity
  ring
/-- Since `p2R13Exact ≥ 0`, the R1.3 correction cannot destroy a nonnegative base net. -/
theorem netQuantity_p2_nonneg_of_base_nonneg (G h : ℝ)
    (hbase : 0 ≤ G - Real.log h) :
    0 ≤ netQuantity G h (p2NetCorrections T).total := by
  rw [netQuantity_p2_eq]
  have hR13 : 0 ≤ p2R13Exact T := p2R13Exact_nonneg T
  linarith
/-- Conversely, a negative net forces the base net to be below `-p2R13Exact`. -/
theorem netQuantity_p2_neg_imp_base_lt (G h : ℝ)
    (hneg : netQuantity G h (p2NetCorrections T).total < 0) :
    G - Real.log h < -p2R13Exact T := by
  rw [netQuantity_p2_eq] at hneg
  linarith
/-- Exact missing identification between the R3.7 source masses and the P2 root data. -/
def R37R13MassIdentification (massL massQ lambda qhat : ℝ) : Prop :=
  Real.log massL - Real.log massQ = Real.log lambda - Real.log qhat
/-- If the mass identification holds, the source net comparison reduces to the
P2 R1.3 mass difference. -/
theorem sourceNetComparison_of_massIdentification
    {massL massQ lambda qhat corrections : ℝ}
    (hid : R37R13MassIdentification massL massQ lambda qhat)
    (hpoint : 0 ≤ Real.log lambda - Real.log qhat)
    (hR13 : Real.log lambda - Real.log qhat ≤ corrections) :
    0 ≤ Real.log massL - Real.log massQ + corrections := by
  unfold R37R13MassIdentification at hid
  linarith
def p2NetMissing : List String :=
  [ "R37R13MassIdentification: identify log mass(L_H) - log mass(Q) with log lambda - log qhat",
    "actual trace-duality coefficient from R3.6 into the correction term",
    "native q reading identification (P2QNativeReadingGap)" ]
theorem p2NetMissing_length : p2NetMissing.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3NetGainP2Actual
end