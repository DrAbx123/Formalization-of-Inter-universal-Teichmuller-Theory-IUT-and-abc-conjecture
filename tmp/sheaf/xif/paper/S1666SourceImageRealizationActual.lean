import tmp.sheaf.xif.paper.S1650RouteFQMarkActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-! # S1666: actual SourceImageRealization for the S1487 faithful C

The S1487/S1650 faithful input is built from the source Haar actual shear
strip: `Mon v = SourceHaarActualValueMonoid` and `thetaPacket.q = 1`.
Therefore the actual positive-real action of the concrete model
`sourceHaarActualPositiveRealAction` (constant 1) is a monoid hom whose
degree at q is `log 1 = 0`, exactly the degree-faithfulness required by
`SourceImageRealization`.  This constructs the missing R, hence the Route F
q mark unconditionally at this C.  No fake realization or arbitrary action is
used; the action is the actual source-Haar model action.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1666SourceImageRealizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S1650RouteFQMarkActual

universe u
variable {l : PrimeGeFive}

/-- The concrete q-parameter of the S1487 faithful theater is 1. -/
theorem S1666_thetaPacket_q_eq_one :
    ((S1650Input (l := l)).theaterAt 0 0).thetaPacket.q = 1 := by
  rfl

/-- Actual SourceImageRealization at any place of the S1487 faithful C. -/
noncomputable def S1666SourceImageRealization
    (v : S1487W) :
    (S1650Input (l := l)).SourceImageRealization v where
  posRealAction := sourceHaarActualPositiveRealAction
  degree_of_q := by
    have hq : ((S1650Input (l := l)).theaterAt 0 0).thetaPacket.q = 1 := rfl
    rw [hq, Real.log_one]
    simp [sourceHaarActualPositiveRealAction]
    exact (S1650Input (l := l)).logDegreeAt_one 0 0 v

/-- The actual Route F q mark, with R supplied by the source-Haar action. -/
noncomputable def S1666QMark
    (n : ThetaPilotCarrier l) :
    (S1650Input (l := l)).ThetaPilotPoint (S1650Place) :=
  S1650QMark (l := l) (S1666SourceImageRealization (l := l) S1650Place) n

end LeanFormal.IUT.XiFPaper.S1666SourceImageRealizationActual

end
