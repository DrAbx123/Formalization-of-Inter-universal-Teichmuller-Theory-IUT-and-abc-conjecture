import tmp.sheaf.xif.paper.Mzk1P3NetGainLogActual
import tmp.sheaf.xif.paper.Mzk1P2RelativeMassActual
/-! P3 (R3.7): corrections decomposition and P2 (R1.3) mass-difference interface. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NetGainCorrectionsActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
/-- Named correction terms in the R3.7 net quantity. -/
structure NetCorrections where
  normRatio : ℝ
  degreeWeight : ℝ
  referenceMassDiff : ℝ
/-- Total correction entering `netQuantity`. -/
def NetCorrections.total (C : NetCorrections) : ℝ :=
  C.normRatio + C.degreeWeight + C.referenceMassDiff
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]
/-- The net quantity only sees the total correction. -/
theorem netQuantity_corrections_eq (G h : ℝ) (C : NetCorrections) :
    netQuantity G h C.total = G - Real.log h + C.normRatio + C.degreeWeight + C.referenceMassDiff := by
  unfold netQuantity NetCorrections.total
  ring
/-- Sign condition: nonnegativity is equivalent to a lower bound on `G - log h`. -/
theorem netQuantity_corrections_nonneg_iff (G h : ℝ) (C : NetCorrections) :
    0 ≤ netQuantity G h C.total ↔
      -(C.normRatio + C.degreeWeight + C.referenceMassDiff) ≤ G - Real.log h := by
  rw [netQuantity_corrections_eq]
  constructor <;> intro hh <;> linarith
-- P2 (R1.3) mass-difference interface
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- P2 R1.3 enters R3.7 only as the `referenceMassDiff` correction. -/
def NetCorrections.withP2R13 (C : NetCorrections) : NetCorrections :=
  { C with referenceMassDiff := C.referenceMassDiff + p2RExact T }
theorem netQuantity_withP2R13_eq (G h : ℝ) (C : NetCorrections) :
    netQuantity G h (C.withP2R13 T).total =
      netQuantity G h C.total + p2RExact T := by
  unfold NetCorrections.withP2R13 NetCorrections.total netQuantity
  ring
theorem netQuantity_withP2R13_nonneg_iff (G h : ℝ) (C : NetCorrections) :
    0 ≤ netQuantity G h (C.withP2R13 T).total ↔
      -p2RExact T ≤ netQuantity G h C.total := by
  rw [netQuantity_withP2R13_eq]
  constructor <;> intro hh <;> linarith
end LeanFormal.IUT.XiFPaper.Mzk1P3NetGainCorrectionsActual
end