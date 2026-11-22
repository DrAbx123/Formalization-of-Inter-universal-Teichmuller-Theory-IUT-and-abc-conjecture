import tmp.sheaf.xif.paper.Mzk1PaperIQCarrierInterfaceActual
import tmp.sheaf.xif.paper.Mzk1HullUBPaperBoxActual
import tmp.sheaf.xif.paper.Mzk1HullUpperBoundInterfaceActual
import tmp.sheaf.xif.paper.Mzk1P3DictDCurveDataSourceActual

/-!
# P7 #8 missing rows: actual inhabitants where possible

Row 2 (paper carrier IQ realization): the actual C3 IQ span gives a
PaperIQCarrierData inhabitant with carrier := actualC3LogShellTensorIQ C3
and carrier_eq := rfl.  This is actual C3 data, not a toy.

Row 7 (hull upper bound): the actual main-term bound plus paperBox yields
HullUpperBound for the actual normalizedLog hull with the explicit constant
C0 = (5/4)(log d + log f).  This is a real inhabitant of the interface, but
NOT the paper C0=0 exact bound; the paper exact bound remains GAP.

Rows 1,3,4,5,6 cannot be inhabited from the current actual data; see
coord/P7-CONTRACT-MISSING7-STATUS.md for the exact obstructions.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7MissingRowsWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperIQCarrierInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBPaperBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUpperBoundInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1MainTermActualBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual

universe u

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Row 2: actual IQ carrier realization from the C3 Q-span. -/
noncomputable def paperIQCarrierData_actual :
    PaperIQCarrierData (C3 := C3) where
  carrier := actualC3LogShellTensorIQ C3
  carrier_eq := rfl

theorem paperIQCarrierData_nonempty : Nonempty (PaperIQCarrierData (C3 := C3)) :=
  ⟨paperIQCarrierData_actual C3⟩

variable {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Row 7: actual hull upper bound with explicit C0 = (5/4)(log d + log f).
This is NOT the paper C0=0 exact bound. -/
theorem hullUpperBound_actual (M : CurveData ι) (E : ι) :
    HullUpperBound (rootExtensionProductNormalizedLog T (s1902Hull T))
      (l.value : Real) (M.disc E : Real) (M.cond E : Real)
      ((5 / 4) * (Real.log (M.disc E : Real) + Real.log (M.cond E : Real))) := by
  have h := normalizedLog_hull_le_paperBox (T := T) (l := l) M E
  rw [paperBox_eq] at h
  unfold HullUpperBound
  have hEq : ((l.value : Real) + 5) / 4 *
        (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) + 0 =
      (1 / 4) * (l.value : Real) *
          (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) +
        (5 / 4) * (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) := by
    ring
  rw [hEq] at h
  exact h

#print axioms paperIQCarrierData_nonempty
#print axioms hullUpperBound_actual

end LeanFormal.IUT.XiFPaper.Mzk1P7MissingRowsWitnessActual
