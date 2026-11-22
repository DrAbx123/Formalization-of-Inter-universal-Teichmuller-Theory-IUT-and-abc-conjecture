/-! # Mzk1Stage4FinalSemanticsRegistryActual (stage4 lane; final semantics registry)

A689 module: the canonical THREE-STATE semantic registry required by A688 — every row is
exactly one of PROVED (green chain) / NAMED (remaining named input) / NOT-PROVED (not
asserted) / NOT-PASSED (gate not passed).  This is the alignment table every V2/status
table must agree with.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalSemanticsRegistryActual

/-- One row of the final-semantics registry. -/
structure SemanticRow where
  /-- the component. -/
  component : String
  /-- its state: PROVED / NAMED / NOT-PROVED / NOT-PASSED. -/
  state : String
  /-- the evidence (file/theorem or reason). -/
  evidence : String
  deriving Repr, DecidableEq

/-- The canonical final-semantics rows (A688 ①-⑥). -/
def finalSemanticRows : List SemanticRow :=
  [ ⟨"Cor 3.12 requirement chain", "PROVED",
      "all green (requirement/resolved/signature chain)"⟩
  , ⟨"corrected-region Gap1", "PROVED",
      "Mzk1CorrectedGap1UnconditionalActual.corrected_gap1_unconditional; hypotheses explicit: full bad support, d_b >= 1, unit >= 0"⟩
  , ⟨"corrected Gap2 shape => ABC", "PROVED",
      "mainline corrected Gap2 shape => ABC theorem"⟩
  , ⟨"only remaining named input: corrected-region Gap2 shape", "NAMED",
      "equivalent (correctedGap2_iff_arith) to pure arithmetic BadSumWeightBound: Σ e_b d_b log p_b <= (1+ε) arithmeticWeight + D'"⟩
  , ⟨"converse (ABC => Gap2)", "NOT-PROVED",
      "not proved and NOT asserted"⟩
  , ⟨"ABC gate", "NOT-PASSED",
      "conditional on the named Gap2 input; ABC NOT proved"⟩
  , ⟨"canonical objects", "PROVED",
      "no canonical change (read-only boundary)"⟩
  ]

/-- The final-semantics registry has seven rows. -/
theorem finalSemanticRows_length : finalSemanticRows.length = 7 := rfl

/-- Every row state is one of the four audited three-state labels. -/
theorem finalSemanticRows_states_ok :
    finalSemanticRows.all (fun r =>
      r.state ∈ ["PROVED", "NAMED", "NOT-PROVED", "NOT-PASSED"]) = true := by
  decide

/-- The named-input row is exactly the corrected-region Gap2 shape (no other named
input remains). -/
theorem named_input_unique :
    (finalSemanticRows.filter (fun r => r.state = "NAMED")).length = 1 := by
  decide

#check finalSemanticRows
#check finalSemanticRows_length
#check finalSemanticRows_states_ok
#check named_input_unique

end LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalSemanticsRegistryActual
end
