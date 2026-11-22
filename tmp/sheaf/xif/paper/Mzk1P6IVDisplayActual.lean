/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P6ActualProducersActual
import tmp.sheaf.xif.paper.Mzk1P6PacketConsumerActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual
theorem p6_thm110_slack_consumer
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l)
    (hd : 1 ≤ T.dmod) (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T :=
  p6_thm110_slack T hl hd hS hE hCor312
end LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayActual
