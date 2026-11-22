import tmp.sheaf.xif.paper.Mzk1Cor312HqnegDischargedActual
import tmp.sheaf.xif.paper.Mzk1HqnegHullModelActual
import tmp.sheaf.xif.paper.Mzk1HqnegCleanGateShaActual

/-!
# shehdd A606/A607 HqnegDischarged acceptance gate (log-only, Sha)

## Verdict (updated after mainline fix)
**PASS.**  Mainline's `Mzk1Cor312HqnegDischargedActual` is now green (olean
present); its latest watchdog run ends with the axiom line
`cor312_hqneg_discharged depends on axioms: [propext, Classical.choice, Quot.sound]`
(no `sorryAx`).  The earlier `@canonicalHqneg ?m hq` type mismatch and `sorryAx`
line in the accumulated log are from superseded versions; mainline has since
made the call explicit `canonicalHqneg (T := T) (qRead := qRead) hq`.

This gate imports the discharged theorem and checks its axioms directly, together
with the hull-owned hqneg model (`Mzk1HqnegHullModelActual`) and shehdd's
conditional hqneg theorems.  No new declarations.
-/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.canonicalHqneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.volModel_strict
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.qPilot_volume_lt_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual.requirement_strict_signed
