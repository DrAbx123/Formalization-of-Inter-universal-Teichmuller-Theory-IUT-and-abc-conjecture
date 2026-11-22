/-! SUPERSEDED (A481): the value-realization carrier (realLineHullData) route is mathematically invalid per SourceHullInterfaceDischarge F2 (hull volume = top / paper-shaped input unsatisfiable). Kept for record only; NOT a solution. Superseded by Mzk1LiteralIQCarrierActual (literal IQ carrier). -/
import tmp.sheaf.xif.paper.S3135ComparisonAssemblyActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! Mainline (endgame construction): build the STANDARD per-epsilon comparison data
  `Cor312EpsilonArithmeticComparison realLineHullData eps` from the S3135 realized
  carrier, discharging both named gap fields with real proofs.  The single explicit
  named input remains `IUTIVSection2UniformDisplayFamily` (section-2 display).
  From the per-epsilon family we obtain the bridge interface inhabitant and ABC. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StandardComparisonConstructionActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual

/-- Standard per-epsilon comparison at the realized carrier from the display family. -/
def standardEpsilonComparison (hf : IUTIVSection2UniformDisplayFamily)
    (eps : Real) (heps : 0 < eps) :
    Cor312EpsilonArithmeticComparison realLineHullData eps where
  logShellPoint := qPilotDisplayPoint
  height_le_normalizedRegionVolume := by
    intro a b c habc
    rw [regionVolume_qPilotDisplayPoint, ENNReal.toReal_ofReal (qPilotDisplayPoint_nonneg a b c)]
    have hheight := height_le_qPilotDisplayPoint habc
    have hnn := qPilotDisplayPoint_nonneg a b c
    have hmul : 0 ≤ eps * qPilotDisplayPoint a b c := mul_nonneg heps.le hnn
    nlinarith [hheight, hmul]
  regionVolume_le_normalizedWeight := by
    obtain ⟨l, dmod, emod, eta, Dbase, hl, hd, he, heta, hslope, hconst, hdisp⟩ :=
      hf eps heps
    refine ⟨20 * (emod * l + eta) + freyDiscrepancy, fun a b c habc => ?_⟩
    rw [regionVolume_qPilotDisplayPoint, hullVolume_eq, ENNReal.toReal_zero, add_zero,
      ENNReal.toReal_ofReal (qPilotDisplayPoint_nonneg a b c)]
    have hdisp' := hdisp a b c habc
    have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
    have hmul : (20 * dmod / l) * arithmeticWeight (abcRationalPoint a c) ≤
        eps * arithmeticWeight (abcRationalPoint a c) :=
      mul_le_mul_of_nonneg_right hslope hw
    have hq : qPilotDisplayPoint a b c =
        (1 / 6) * freyLogQ a b c + freyDiscrepancy := rfl
    rw [hq]
    nlinarith [hdisp', hw, hmul]

theorem nonempty_bridgeInterface_of_displayFamily
    (hf : IUTIVSection2UniformDisplayFamily) :
    Nonempty (Cor312ToABCBridgeInterface.{0}) :=
  ⟨{ carrier := Real
     hullData := realLineHullData
     epsilonComparison := fun eps heps => standardEpsilonComparison hf eps heps }⟩

theorem abcConjecture_of_displayFamily
    (hf : IUTIVSection2UniformDisplayFamily) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture
    { carrier := Real
      hullData := realLineHullData
      epsilonComparison := fun eps heps => standardEpsilonComparison hf eps heps }

end

end LeanFormal.IUT.XiFPaper.Mzk1StandardComparisonConstructionActual