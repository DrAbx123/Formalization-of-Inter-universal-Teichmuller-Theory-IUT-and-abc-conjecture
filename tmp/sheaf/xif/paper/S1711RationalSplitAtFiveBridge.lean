import tmp.sheaf.xif.paper.S1713SplitReductionActual
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

/-- The canonical S1667 punctured curve has split multiplicative reduction at
the rational place five. -/
theorem S1711RationalSplitAtFive :
    S1667Punctured.HasSplitMultiplicativeReductionAt concreteFivePlace :=
  LeanFormal.IUT.XiFPaper.S1713SplitReductionActual.S1713_splitMultiplicativeReductionAtFive

#print axioms S1711RationalSplitAtFive
