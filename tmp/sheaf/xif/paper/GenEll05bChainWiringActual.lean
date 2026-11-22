import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import tmp.sheaf.xif.paper.GenEll01bHeightLayerActual
import tmp.sheaf.xif.paper.GenEll01cHeightMulEstimatesActual
import tmp.sheaf.xif.paper.GenEll02Prop14Actual
import tmp.sheaf.xif.paper.GenEll02bProofActual
import tmp.sheaf.xif.paper.GenEll02cFinitenessInputActual
import tmp.sheaf.xif.paper.GenEll03Prop16Actual
import tmp.sheaf.xif.paper.GenEll03bProofActual
import tmp.sheaf.xif.paper.GenEll04Prop17Actual
import tmp.sheaf.xif.paper.GenEll04bProp17ChainActual
import tmp.sheaf.xif.paper.GenEll04cDifferentInputsActual
import tmp.sheaf.xif.paper.GenEll09BDToolsActual

/-! # GenEll05b: wiring map for Theorem 2.1 (ii)⇒(i) inputs (abc statements) -/

namespace LeanFormal.IUT.XiFPaper.GenEll05bChainWiringActual

open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open LeanFormal.IUT.XiFPaper.GenEll02Prop14Actual
open LeanFormal.IUT.XiFPaper.GenEll02bProofActual
open LeanFormal.IUT.XiFPaper.GenEll03Prop16Actual
open LeanFormal.IUT.XiFPaper.GenEll04Prop17Actual
open LeanFormal.IUT.XiFPaper.GenEll04cDifferentInputsActual

/-- Import-validation / wiring rows: each `Theorem21ReductionInputs` field is backed
by a concrete abc declaration (Proven vs Exact-paper-input). -/
def GenEll05bWiringMap : List (String × String × String) :=
  [ ("(a) compactnessInput", "not yet formalized (topology of X(Q_v)^d); stage4/abc pending", "input"),
    ("(b) mzk1NoncriticalBelyi", "stage4 Mzk1 Thm 2.5/Cor 3.2 statement (to import when green)", "input"),
    ("(c) compactlyBoundedFromPhi", "construction from phi-images (paper)", "input"),
    ("(d1) prop16LogCondLeHeight", "GenEll03Prop16Actual.Prop16ConductorBoundedByHeight + GenEll03b proof (from pointwise bounded-|s| input)", "statement+proof"),
    ("(d2) prop17LogDiffCondLe", "GenEll04Prop17Actual.Proposition17Statement / Prop17LogDiffInequality + GenEll04b chain", "statement+assembly"),
    ("(d2') different theory", "GenEll04cDifferentInputsActual.Prop17DifferentTheoryInput (corpus 565-602)", "exact paper-input"),
    ("(d3) prop14HeightComparison", "GenEll02Prop14Actual.Proposition14Statement + prop14_additive_of_statement / prop14_bdclass_of_statement + GenEll02b extractions", "statement+extractions"),
    ("(d3') finiteness", "GenEll02cFinitenessInputActual.Prop14FinitenessPaperInput (class B)", "exact paper-input"),
    ("(d4) epsilonPrelude", "GenEll05Theorem21Actual.paper_epsilon_absorption (PROVED arithmetic)", "proven"),
    ("height-layer facts", "GenEll01bHeightLayerActual.s3135_hBox_nonneg; GenEll01cHeightMulEstimatesActual mul/subadditivity reuse", "proven reuse"),
    ("BD chain tools", "GenEll09BDToolsActual.isBDLe_add/isBDLe_of_le/isBDLe_add_const_left/isBDLe_neg_swap", "proven tools") ]

theorem GenEll05bWiringMap_length : GenEll05bWiringMap.length = 11 := rfl

#check Proposition14Statement
#check Prop16ConductorBoundedByHeight
#check Proposition17Statement
#check Prop17DifferentTheoryInput
#check paper_epsilon_absorption
#check LeanFormal.IUT.XiFPaper.GenEll09BDToolsActual.isBDLe_add

end LeanFormal.IUT.XiFPaper.GenEll05bChainWiringActual
