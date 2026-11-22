import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellFrobeniusAction

/-!
# Mzk1FrobeniusActionConsumerActual — consumer re-exports over the Example36 log-shell
Frobenius action (tree asset, OLEAN_FRESH). Genuine object/lemma re-exports only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobeniusActionConsumerActual

open LeanFormal.IUT

/-- Consumer: the principal-unit Frobenius endomorphism (p-th power). -/
def consumer_principalUnitFrobenius :=
  @principalUnitFrobenius

/-- Consumer: its monoid-hom packaging. -/
def consumer_principalUnitFrobeniusMonoidHom :=
  @principalUnitFrobeniusMonoidHom

/-- Consumer: the induced log-shell Frobenius endomorphism. -/
def consumer_principalUnitLogShellFrobenius :=
  @principalUnitLogShellFrobenius

/-- Consumer: the tree's log-shell Frobenius action summary theorem. -/
def consumer_frobeniusAction_summary :=
  @example36LogShellFrobeniusAction_summary

/-- Consumer: p-multiplication keeps the principal-unit log-shell stable. -/
def consumer_principalUnitLogShell_p_mul_mem :=
  @principalUnitLogShell_p_mul_mem

#check consumer_principalUnitFrobenius
#check consumer_principalUnitFrobeniusMonoidHom
#check consumer_principalUnitLogShellFrobenius
#check consumer_frobeniusAction_summary
#check consumer_principalUnitLogShell_p_mul_mem

end LeanFormal.IUT.XiFPaper.Mzk1FrobeniusActionConsumerActual
end
