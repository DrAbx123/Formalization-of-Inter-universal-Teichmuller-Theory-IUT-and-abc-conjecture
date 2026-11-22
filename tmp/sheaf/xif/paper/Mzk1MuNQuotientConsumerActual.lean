import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceLogShellMuNQuotientCarrier

/-!
# Mzk1MuNQuotientConsumerActual — consumer theorems over the source log-shell muN quotient
carrier (tree asset, OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1MuNQuotientConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

universe u

/-- Consumer: kernel of the reduced quotient map is the torsion subgroup. -/
theorem consumer_muNQuotientMap_ker (D : SourceLogShellDatum.{u}) :
    MonoidHom.ker D.muNQuotientMap = CommGroup.torsion D.Units :=
  D.muNQuotientMap_ker

/-- Consumer: the reduced quotient map is surjective. -/
theorem consumer_muNQuotientMap_surjective (D : SourceLogShellDatum.{u}) :
    Function.Surjective D.muNQuotientMap :=
  D.muNQuotientMap_surjective

/-- Consumer: reduced weight-N convention: weightNLog N (u^N) = log u. -/
theorem consumer_weightNLog_pow (D : SourceLogShellDatum.{u}) (N : ℕ) (hN : N ≠ 0)
    (u : D.Units) : D.weightNLog N (u ^ N) = (D.logMap u).toAdd :=
  D.weightNLog_pow N hN u

/-- Consumer: definition of the reduced weight-N logarithm. -/
theorem consumer_weightNLog_def (D : SourceLogShellDatum.{u}) (N : ℕ) (u : D.Units) :
    D.weightNLog N u = (N : D.K)⁻¹ * (D.logMap u).toAdd := rfl

/-- Consumer: the muN power endomorphism exists for every N. -/
def consumer_muNPowEnd (D : SourceLogShellDatum.{u}) (N : ℕ) :
    D.muNQuotient →* D.muNQuotient :=
  D.muNPowEnd N

#check consumer_muNQuotientMap_ker
#check consumer_muNQuotientMap_surjective
#check consumer_weightNLog_pow
#check consumer_weightNLog_def
#check consumer_muNPowEnd

end LeanFormal.IUT.XiFPaper.Mzk1MuNQuotientConsumerActual
end
