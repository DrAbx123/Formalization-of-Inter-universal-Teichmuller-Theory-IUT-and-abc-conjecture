set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1LegacyN8GapStatementLayerActual — legacy N8 gap statement layer

A474: real Lean statement layer for the legacy N8/closure GAP nodes (C1-C10 and
groups 1-6, L0.2/L0.4/L0.5/L0.3, L1-F1/F7). Type-level structures with
projection theorems; no sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1LegacyN8GapStatementLayerActual

structure N8SourceInputsStatement where
  c0_target_signature : Prop
  c1_source_input_binding : Prop
  group1_source_objects : Prop

structure N8SourceKummerStatement where
  c2_source_log_kummer : Prop
  c3_source_pilot_region : Prop
  group2_log_k1k2 : Prop
  group3_q_theta_pilot : Prop

structure N8SourceOutputStatement where
  c4_source_witnessed_output : Prop
  c5_algorithm_compatibility : Prop
  c6_actual_iq_data : Prop
  c7_holomorphic_hull : Prop

structure N8EvaluationStatement where
  c8_degree_comparison_iq : Prop
  c9_final_evaluation_capsule : Prop
  c9_output_region_source_route : Prop
  c10_assembly : Prop
  c10_named_assembly : Prop

structure N8Group456Statement where
  group4_kummer_log_volume_compat : Prop
  group5_ipl_she_apt : Prop
  group6_hull_degree : Prop

structure LegacyL0Statement where
  l0_2_local_field_variable_change : Prop
  l0_2_tate_parameter : Prop
  l0_4_log_comparison : Prop
  l0_5_source_theta : Prop
  l03_g2_milestone : Prop

structure LegacyL1Statement where
  l1_f1_equivalence : Prop
  l1_f7_tate_uniformization : Prop

theorem n8_sourceInputs_c1 (H : N8SourceInputsStatement) : H.c1_source_input_binding := H.c1_source_input_binding
theorem n8_sourceKummer_c2 (H : N8SourceKummerStatement) : H.c2_source_log_kummer := H.c2_source_log_kummer
theorem n8_sourceOutput_c7 (H : N8SourceOutputStatement) : H.c7_holomorphic_hull := H.c7_holomorphic_hull
theorem n8_evaluation_c10 (H : N8EvaluationStatement) : H.c10_assembly := H.c10_assembly
theorem n8_group456_g5 (H : N8Group456Statement) : H.group5_ipl_she_apt := H.group5_ipl_she_apt
theorem legacyL0_sourceTheta (H : LegacyL0Statement) : H.l0_5_source_theta := H.l0_5_source_theta
theorem legacyL1_f7 (H : LegacyL1Statement) : H.l1_f7_tate_uniformization := H.l1_f7_tate_uniformization

def legacyN8GapRows : List (String × String × String) :=
  [ ("C0-C1 + group1", "GAP (statement layer)", "N8SourceInputsStatement"),
    ("C2-C3 + groups2-3", "GAP (statement layer)", "N8SourceKummerStatement"),
    ("C4-C7", "GAP (statement layer)", "N8SourceOutputStatement"),
    ("C8-C10", "GAP (statement layer)", "N8EvaluationStatement"),
    ("groups4-6", "GAP (statement layer)", "N8Group456Statement"),
    ("L0.2-L0.5/L0.3", "GAP (statement layer)", "LegacyL0Statement"),
    ("L1-F1/F7", "GAP (statement layer)", "LegacyL1Statement") ]

theorem legacyN8GapRows_length : legacyN8GapRows.length = 7 := rfl

#check legacyN8GapRows_length

end LeanFormal.IUT.XiFPaper.Mzk1LegacyN8GapStatementLayerActual
end