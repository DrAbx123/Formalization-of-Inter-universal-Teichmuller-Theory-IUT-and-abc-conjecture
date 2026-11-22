import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1LogShellCarrierConsumerActual — consumer theorems over the source log-shell carrier
(tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellCarrierConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

universe u

/-- Consumer: p* is positive. -/
theorem consumer_pStar_pos (D : SourceLogShellDatum.{u}) : 0 < D.pStar :=
  D.pStar_pos

/-- Consumer: p* is nonzero. -/
theorem consumer_pStar_ne_zero (D : SourceLogShellDatum.{u}) : D.pStar ≠ 0 :=
  D.pStar_ne_zero

/-- Consumer: p* is nonzero as cast into the log-coordinate field. -/
theorem consumer_pStar_ne_zero_cast (D : SourceLogShellDatum.{u}) :
    (D.pStar : D.K) ≠ 0 :=
  D.pStar_ne_zero_cast

/-- Consumer: the pre-log-shell (invariant image) is inside the unit layer. -/
theorem consumer_preLogShell_subset_unitLayer (D : SourceLogShellDatum.{u}) :
    D.preLogShell ⊆ D.unitLayer :=
  D.preLogShell_subset_unitLayer

/-- Consumer: the log-shell is the p*-inverse-scaled pre-log-shell. -/
theorem consumer_logShell_def (D : SourceLogShellDatum.{u}) :
    D.logShell = {a : D.K | (D.pStar : D.K) * a ∈ D.preLogShell} := rfl

#check consumer_pStar_pos
#check consumer_pStar_ne_zero
#check consumer_pStar_ne_zero_cast
#check consumer_preLogShell_subset_unitLayer
#check consumer_logShell_def

end LeanFormal.IUT.XiFPaper.Mzk1LogShellCarrierConsumerActual
end
