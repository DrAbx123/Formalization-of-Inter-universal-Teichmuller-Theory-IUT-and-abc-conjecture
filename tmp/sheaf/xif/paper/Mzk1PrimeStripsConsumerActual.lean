import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsConstruction

/-!
# Mzk1PrimeStripsConsumerActual — consumer re-exports over the prime-strip construction
(tree asset, OLEAN_FRESH). Genuine object/link re-exports only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsConsumerActual

open LeanFormal.IUT

/-- Consumer: the prime-strip link structure. -/
def consumer_FPrimeStripLink :=
  @FPrimeStripLink

/-- Consumer: identity prime-strip link. -/
def consumer_link_refl :=
  @FPrimeStripLink.refl

/-- Consumer: composition of prime-strip links. -/
def consumer_link_trans :=
  @FPrimeStripLink.trans

/-- Consumer: finite-to-global unit link. -/
def consumer_finiteToGlobalUnitLink :=
  @finiteToGlobalUnitLink

/-- Consumer: finite-to-global integral link. -/
def consumer_finiteToGlobalIntegralLink :=
  @finiteToGlobalIntegralLink

/-- Consumer: finite-to-global integral-to-unit composite link. -/
def consumer_finiteIntegralToGlobalUnitLink :=
  @finiteIntegralToGlobalUnitLink

#check consumer_FPrimeStripLink
#check consumer_link_refl
#check consumer_link_trans
#check consumer_finiteToGlobalUnitLink
#check consumer_finiteToGlobalIntegralLink
#check consumer_finiteIntegralToGlobalUnitLink

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripsConsumerActual
end
