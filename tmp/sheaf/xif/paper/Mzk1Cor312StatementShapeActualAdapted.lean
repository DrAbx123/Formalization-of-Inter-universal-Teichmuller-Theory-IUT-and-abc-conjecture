import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual

/-! Mainline: Cor 3.12 paper-statement shape and its equivalence to the S2717 upper gap. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActualAdapted

open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual

/-- Cor 3.12 paper statement shape (full target form). -/
def Cor312StatementShape : Prop := PaperCor312Full

theorem cor312StatementShape_iff_upperGap :
    Cor312StatementShape ↔ S2717UpperGap :=
  S2717_full_iff_hupper

theorem upperGap_of_cor312Statement (h : Cor312StatementShape) :
    S2717UpperGap :=
  cor312StatementShape_iff_upperGap.mp h

theorem cor312Statement_of_upperGap (h : S2717UpperGap) :
    Cor312StatementShape :=
  cor312StatementShape_iff_upperGap.mpr h

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActualAdapted