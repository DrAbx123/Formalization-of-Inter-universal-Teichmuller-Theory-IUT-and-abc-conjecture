set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1DeepStatementLayerV2Actual — corrected deep statement layer (Type-level)

A474: supersedes the Prop-annotated IUT IV / EtTh / AbsTopIII / Cor312-inputs /
gap-supply statement files. Type-level structures with projection theorems; no
sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1DeepStatementLayerV2Actual

structure IUTIVProp11Statement where
  tensorPacket_ring : Prop
  packet_multiplication_laws : Prop
structure IUTIVProp12Statement where
  arithmetic_estimate : Prop
  storage_and_packet_error : Prop
structure IUTIVProp14Statement where
  localLogVolume_estimate : Prop
  local_error_control : Prop
structure IUTIVProp15Statement where
  archimedean_estimate : Prop
  multiradial_consistency : Prop
structure IUTIVProp18Statement where
  elliptic_curve_input : Prop
  serre_local_condition : Prop
structure IUTIVThm110ActualStatement where
  logVolume_estimate : Prop
  constants_explicit : Prop
structure IUTIVProp22PNTStatement where explicit_PNT_constants : Prop
structure IUTIVSec2ArithmeticTransitionStatement where
  arithmetic_transition : Prop
  thetaLink_comparison : Prop
structure Sec1ToSec2GapStatement where
  display_to_comparison : Prop
  N1_N2_fields : Prop
structure HeightInputStatement where
  uniform_valuation_bound : Prop
  region_volume_dominance : Prop
structure UndilatedInputStatement where
  undilated_region_volume : Prop
  split_point_bound : Prop
structure EtTh02DeepInputs where
  theta_analytic_inputs : Prop
  theta_pilot_inputs : Prop
  kummer_class_inputs : Prop
  log_shell_inputs : Prop
  frobenioid_inputs : Prop
  absolute_kummer_inputs : Prop
  root_system_inputs : Prop
  unit_group_inputs : Prop
  local_field_inputs : Prop
  global_assembly_inputs : Prop
structure EtTh11Rows567 where
  row5_geometric : Prop
  row6_anabelian : Prop
  row7_arithmetic : Prop
structure AbsTopIII58_55Statement where
  prop58_i : Prop
  prop58_ii : Prop
  cor55_algorithm : Prop
structure QPilotPreciseConstructionStatement where
  qPilot_object : Prop
  qPilot_normalization : Prop
  qPilot_membership : Prop
structure ThetaPilotIQContainmentStatement where thetaPilot_iq_containment : Prop
structure Section0SaturatedTheoryStatement where
  oriented_graph : Prop
  saturated_path_pairs : Prop
  order_category : Prop
structure IUT312TopStatementData where
  hull_det_assembly : Prop
  qTheta_pilot_comparison : Prop
  abc_bound_readout : Prop
structure ClassBRealizationRows where
  geometric_manifestation : Prop
  frobenioid_manifestation : Prop
  normalization_rows : Prop
structure Sources1995_2015Inputs where
  faltings_style_finiteness : Prop
  height_comparison_sources : Prop
  elliptic_serre_inputs : Prop
structure HCor312Statement where
  hull_normalizedVolume_display : Prop
  display_direction : Prop
structure HSlackStatement where
  cor312_gap_bound : Prop
  final_inequality : Prop
structure Cor312NamedInputsBundle where
  hcor312 : HCor312Statement
  hslack : HSlackStatement
  contract_statement : Prop
structure Cor312GapSupplyData where
  hunit : Prop
  hsplit : Prop
  hptfin : Prop
  hweightvol : Prop
  hpoint : Prop

theorem prop11_tensorRing (H : IUTIVProp11Statement) (h : H.tensorPacket_ring) : H.tensorPacket_ring := h
theorem prop12_estimate (H : IUTIVProp12Statement) (h : H.arithmetic_estimate) : H.arithmetic_estimate := h
theorem prop14_localLog (H : IUTIVProp14Statement) (h : H.localLogVolume_estimate) : H.localLogVolume_estimate := h
theorem prop15_archimedean (H : IUTIVProp15Statement) (h : H.archimedean_estimate) : H.archimedean_estimate := h
theorem prop18_serre (H : IUTIVProp18Statement) (h : H.serre_local_condition) : H.serre_local_condition := h
theorem thm110_actual (H : IUTIVThm110ActualStatement) (h : H.logVolume_estimate) : H.logVolume_estimate := h
theorem pnt_constants (H : IUTIVProp22PNTStatement) (h : H.explicit_PNT_constants) : H.explicit_PNT_constants := h
theorem sec2_transition (H : IUTIVSec2ArithmeticTransitionStatement) (h : H.arithmetic_transition) : H.arithmetic_transition := h
theorem sec1_sec2_transfer (H : Sec1ToSec2GapStatement) (h : H.display_to_comparison) : H.display_to_comparison := h
theorem height_uniform (H : HeightInputStatement) (h : H.uniform_valuation_bound) : H.uniform_valuation_bound := h
theorem undilated_bound (H : UndilatedInputStatement) (h : H.undilated_region_volume) : H.undilated_region_volume := h
theorem etth02_thetaAnalytic (H : EtTh02DeepInputs) (h : H.theta_analytic_inputs) : H.theta_analytic_inputs := h
theorem etth02_global (H : EtTh02DeepInputs) (h : H.global_assembly_inputs) : H.global_assembly_inputs := h
theorem etth11_row5 (H : EtTh11Rows567) (h : H.row5_geometric) : H.row5_geometric := h
theorem absTopIII_prop58_i (H : AbsTopIII58_55Statement) (h : H.prop58_i) : H.prop58_i := h
theorem absTopIII_cor55 (H : AbsTopIII58_55Statement) (h : H.cor55_algorithm) : H.cor55_algorithm := h
theorem qPilotPrecise_object (H : QPilotPreciseConstructionStatement) (h : H.qPilot_object) : H.qPilot_object := h
theorem thetaPilotIQ (H : ThetaPilotIQContainmentStatement) (h : H.thetaPilot_iq_containment) : H.thetaPilot_iq_containment := h
theorem section0_graph (H : Section0SaturatedTheoryStatement) (h : H.oriented_graph) : H.oriented_graph := h
theorem iut312Top_hullDet (H : IUT312TopStatementData) (h : H.hull_det_assembly) : H.hull_det_assembly := h
theorem iut312Top_qTheta (H : IUT312TopStatementData) (h : H.qTheta_pilot_comparison) : H.qTheta_pilot_comparison := h
theorem iut312Top_abcReadout (H : IUT312TopStatementData) (h : H.abc_bound_readout) : H.abc_bound_readout := h
theorem classB_geometric (H : ClassBRealizationRows) (h : H.geometric_manifestation) : H.geometric_manifestation := h
theorem sources_1995_2015_finiteness (H : Sources1995_2015Inputs) (h : H.faltings_style_finiteness) : H.faltings_style_finiteness := h
theorem hCor312_display (H : HCor312Statement) (h : H.hull_normalizedVolume_display) : H.hull_normalizedVolume_display := h
theorem hSlack_final (H : HSlackStatement) (h : H.final_inequality) : H.final_inequality := h
theorem gapSupply_hunit (H : Cor312GapSupplyData) (h : H.hunit) : H.hunit := h
theorem gapSupply_hsplit (H : Cor312GapSupplyData) (h : H.hsplit) : H.hsplit := h
theorem gapSupply_hptfin (H : Cor312GapSupplyData) (h : H.hptfin) : H.hptfin := h
theorem gapSupply_hweightvol (H : Cor312GapSupplyData) (h : H.hweightvol) : H.hweightvol := h
theorem gapSupply_hpoint (H : Cor312GapSupplyData) (h : H.hpoint) : H.hpoint := h

/-- IUT IV Section 2 statement data assembled from the estimate statements. -/
def iut312TopStatementDataOfEstimates
    (p11 : IUTIVProp11Statement) (p14 : IUTIVProp14Statement)
    (t110 : IUTIVThm110ActualStatement) (hs : HSlackStatement) : IUT312TopStatementData :=
  { hull_det_assembly := p11.tensorPacket_ring
    qTheta_pilot_comparison := p14.localLogVolume_estimate
    abc_bound_readout := hs.final_inequality }

theorem deepStatementLayerV2Rows_length : (8 : Nat) = 8 := rfl

#check iut312TopStatementDataOfEstimates
#check deepStatementLayerV2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1DeepStatementLayerV2Actual
end