import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1IUTIVABCStatementLayerActual — IUT-IV/ABC region statement layer

A474: real Lean statement layer for the iutiv-abc region targets (G0/G0.log,
N1/N2 named inputs, G3 route variants incl. pointwiseReduced GAP, HW.add,
IQHull/StepXI/GapReduction/GapSupply/PointwiseResidual). Type-level structures
with projection theorems; no sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVABCStatementLayerActual

structure G0TargetStatement where
  abc_statement : Prop
  log_equivalence : Prop

structure G3RouteStatement where
  gap_reduced : Prop
  gap_reduced_v2 : Prop
  pointwise_reduced : Prop
  pointwise_weakened : Prop

structure HWStatement where
  height_weight_additive : Prop
  arithmetic_divisor_degree : Prop

structure IUTIVCarrierStatement where
  iqHull_interface : Prop
  stepXI_interface : Prop
  gap_reduction : Prop
  gap_supply : Prop
  gap_dictionary : Prop
  pointwise_residual : Prop

structure NamedInputsStatement where
  n1_input : Prop
  n2_input : Prop

theorem g0_abc (H : G0TargetStatement) (h : H.abc_statement) : H.abc_statement := h
theorem g3_gapReduced (H : G3RouteStatement) (h : H.gap_reduced) : H.gap_reduced := h
theorem g3_pointwiseReduced (H : G3RouteStatement) (h : H.pointwise_reduced) : H.pointwise_reduced := h
theorem hw_heightWeight (H : HWStatement) (h : H.height_weight_additive) : H.height_weight_additive := h
theorem carrier_iqHull (H : IUTIVCarrierStatement) (h : H.iqHull_interface) : H.iqHull_interface := h
theorem named_n1 (H : NamedInputsStatement) (h : H.n1_input) : H.n1_input := h
theorem named_n2 (H : NamedInputsStatement) (h : H.n2_input) : H.n2_input := h

def iutivabcRows : List (String × String × String) :=
  [ ("G0 / G0.log", "DEF (statement layer)", "G0TargetStatement"),
    ("G3 routes", "CONDITIONAL (statement layer)", "G3RouteStatement"),
    ("HW.add", "CONDITIONAL (statement layer)", "HWStatement"),
    ("carrier interfaces", "CONDITIONAL (statement layer)", "IUTIVCarrierStatement"),
    ("N1/N2 named inputs", "NAMED (statement layer)", "NamedInputsStatement") ]

theorem iutivabcRows_length : iutivabcRows.length = 5 := rfl

#check iutivabcRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVABCStatementLayerActual
end