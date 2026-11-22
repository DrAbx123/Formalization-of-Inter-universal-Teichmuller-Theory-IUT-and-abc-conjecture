import tmp.sheaf.xif.paper.S2116CommutatorClosedActual

-- S2147: audit of a prosolvable shortcut for M2c.  No elementary
-- prosolvable commutator-closed theorem is formalized; the effective
-- exact input remains bounded commutator width / Nikolov-Segal.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2147M2cProsolvableActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2109M2cCarrierActual
open LeanFormal.IUT.XiFPaper.S2116CommutatorClosedActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact M2c target: commutator closedness at every level. -/
abbrev S2147M2cCommutatorClosedRequired : Prop :=
  M2cFirstMissing (p := p)

/-- The prosolvable shortcut would need this bounded-width input, or an
equivalent commutator-closed theorem not present in the tree. -/
abbrev S2147ProsolvableShortcutRequired : Prop :=
  CommutatorWidthInput (p := p)

theorem S2147_shortcut_sufficient
    (h : S2147ProsolvableShortcutRequired p) :
    S2147M2cCommutatorClosedRequired p :=
  m2cFirstMissing_of_widthInput h

/-- The actual deep inputs isolated by S2116. -/
abbrev S2147TopologicallyFGRequired : Prop :=
  ∀ U : Index p, TopologicallyFinitelyGenerated U

abbrev S2147NikolovSegalWidthRequired : Prop :=
  NikolovSegalCommutatorWidth.{0}

/-- Conditional M2c from the named deep inputs. -/
theorem S2147_m2c_of_nikolovSegal
    (hNS : S2147NikolovSegalWidthRequired)
    (hfg : S2147TopologicallyFGRequired (p := p)) :
    S2147M2cCommutatorClosedRequired p :=
  m2cFirstMissing_of_nikolovSegal hNS hfg

#check S2147M2cCommutatorClosedRequired
#check S2147ProsolvableShortcutRequired
#check S2147_shortcut_sufficient
#check S2147TopologicallyFGRequired
#check S2147NikolovSegalWidthRequired
#check S2147_m2c_of_nikolovSegal

#print axioms S2147_shortcut_sufficient
#print axioms S2147_m2c_of_nikolovSegal

end LeanFormal.IUT.XiFPaper.S2147M2cProsolvableActual

end