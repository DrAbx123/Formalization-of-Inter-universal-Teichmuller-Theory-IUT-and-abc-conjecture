import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import LeanFormal.IUT.IUTI.InitialTheta.Definition31D0D11Aligned
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply

/-!
# Mzk1SchemeSideMapsTreeReuseActual — stage-4 scheme-side maps / stepxi supply nodes
advanced by REUSING existing tree assets

Lead A475 reuse rule: exhaustive search found the tree assets
IUTIV/Estimates/ArithmeticDivisorDegree.lean (place/weight/degree machinery),
IUTI/InitialTheta/Definition31D0D11Aligned.lean (D0-D11 root data) and
IUTIII/.../HolomorphicHull/CardAMPLThetaBoundSupply.lean (Card AMPL theta-bound supply),
all with oleans. The existing tmp interface Mzk1SchemeSideMapsActual.lean is recorded as the
anchor for the stage-4 scheme-side-maps object (its olean is absent at this revision and it is
not duplicated here).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeSideMapsTreeReuseActual

open LeanFormal.IUT

/-- Existing tree IUT IV place/weight machinery (scheme-side/height anchor). -/
def iutivWeightReuse :=
  @weight

/-- Existing tree absolute-norm/cardinality identity (scheme-side/height anchor). -/
def iutivAbsNormReuse :=
  @absNorm_eq_cardQuot

/-- Existing tree IUT III Card AMPL theta-bound supply. -/
def cardAMPLThetaBoundSupplyReuse :=
  @cardAMPLThetaBoundSupply

/-- Existing tree Card AMPL supply certificate. -/
def cardAMPLCertificateReuse :=
  @certificate

/-- Existing tree IUT I initial-theta D0 root data. -/
def sourceD0RootReuse :=
  @D0Root

/-- Scheme-side reuse rows: (target node, existing asset, status). -/
def schemeSideReuseRows : List (String × String × String) :=
  [ ("iut-pre-stage4:D.gap.schemeSideMaps", "Mzk1SchemeSideMapsActual.lean (existing tmp interface; anchor, olean absent)", "REUSE anchor (not duplicated)"),
    ("iutiv height/degree machinery", "ArithmeticDivisorDegree (weight/absNorm/degree)", "REUSE (tree olean)"),
    ("initial-theta D0 root data", "Definition31D0D11Aligned.D0Root", "REUSE (tree olean)"),
    ("stepxi Card AMPL theta-bound supply", "CardAMPLThetaBoundSupply + certificate", "REUSE (tree olean)"),
    ("conditional scheme-side maps", "not asserted (existing interface anchor only)", "NAMED") ]

/-- The scheme-side reuse row record has five rows. -/
theorem schemeSideReuseRows_length : schemeSideReuseRows.length = 5 := rfl

#check iutivWeightReuse
#check iutivAbsNormReuse
#check cardAMPLThetaBoundSupplyReuse
#check cardAMPLCertificateReuse
#check sourceD0RootReuse
#check schemeSideReuseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SchemeSideMapsTreeReuseActual
end
