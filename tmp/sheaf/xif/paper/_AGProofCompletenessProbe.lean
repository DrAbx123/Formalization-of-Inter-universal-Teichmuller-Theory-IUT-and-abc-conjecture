import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_AdelicIndex
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_DivisorClassGroup
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicCurve_Repartitions
import tmp.sheaf.xif.paper.AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange
import tmp.sheaf.xif.paper.AG01CurveFoundationsActual
import tmp.sheaf.xif.paper.AG02bPrincipalDivisorActual
import tmp.sheaf.xif.paper.AG02FunctionFieldActual
import tmp.sheaf.xif.paper.AG02GenusActual
import tmp.sheaf.xif.paper.AG03bSectionsBasicActual
import tmp.sheaf.xif.paper.AG03DivisorsSectionsActual
import tmp.sheaf.xif.paper.AG04bResidueFieldActual
import tmp.sheaf.xif.paper.AG04FiniteDivisorActual
import tmp.sheaf.xif.paper.AG94StepXIBindActual
import tmp.sheaf.xif.paper.AG_FLT_PromotionActual

/-! AG proof-completeness axiom probe (corrected namespaces). -/
#print axioms AlgebraicCurve._root_
#print axioms AlgebraicCurve.adeleBdd_directed
#print axioms AlgebraicCurve.adeleBdd_le_adeleSpace
#print axioms AlgebraicCurve.adeleBdd_mono
#print axioms AlgebraicCurve.adeleSpaceMul_coe
#print axioms AlgebraicCurve.adeleSpaceMul_mul
#print axioms AlgebraicCurve.adeleSpaceMul_one
#print axioms AlgebraicCurve.algebraMap_mem_lSpace_zero
#print axioms AlgebraicCurve.diagonal_mem_adeleBdd_iff
#print axioms AlgebraicCurve.diagonal_mem_adeleSpace
#print axioms AlgebraicCurve.diagonal_mem_globalSub
#print axioms AlgebraicCurve.diagonalHom_apply
#print axioms AlgebraicCurve.diagonalHom_injective
#print axioms AlgebraicCurve.Divisor.degree_single
#print axioms AlgebraicCurve.Divisor.degree_smul
#print axioms AlgebraicCurve.Divisor.mem_degZero
#print axioms AlgebraicCurve.Divisor.mem_principal
#print axioms AlgebraicCurve.Divisor.smul_apply
#print axioms AlgebraicCurve.Divisor.smul_apply_smul
#print axioms AlgebraicCurve.Divisor.smul_def
#print axioms AlgebraicCurve.Divisor.smul_mem_degZero
#print axioms AlgebraicCurve.Divisor.smul_mem_principal
#print axioms AlgebraicCurve.Divisor.smul_single
#print axioms AlgebraicCurve.ell_sub_le_indexOfSpecialty
#print axioms AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase
#print axioms AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell
#print axioms AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty
#print axioms AlgebraicCurve.indexOfSpecialty_eq
#print axioms AlgebraicCurve.lSpace_mono
#print axioms AlgebraicCurve.map_diagonal_lSpace
#print axioms AlgebraicCurve.mem_adeleBdd
#print axioms AlgebraicCurve.mem_adeleSpace_iff
#print axioms AlgebraicCurve.mem_lSpace_iff
#print axioms AlgebraicCurve.mem_lSpace_iff_ord
#print axioms AlgebraicCurve.mem_principalRepartitions_iff
#print axioms AlgebraicCurve.mem_repartitions_of_finite
#print axioms AlgebraicCurve.mem_repartitions_of_finite_ord
#print axioms AlgebraicCurve.mem_repartitions_of_forall_le_exp
#print axioms AlgebraicCurve.mem_repartitionsOf_iff
#print axioms AlgebraicCurve.mem_riemannRochSpace_iff
#print axioms AlgebraicCurve.mem_weilDifferentialModule_iff
#print axioms AlgebraicCurve.mulAdele_apply
#print axioms AlgebraicCurve.mulAdele_globalSub_le
#print axioms AlgebraicCurve.mulAdele_mem_adeleBdd_sub
#print axioms AlgebraicCurve.mulAdele_mem_adeleSpace
#print axioms AlgebraicCurve.mulAdele_mul
#print axioms AlgebraicCurve.mulAdele_one
#print axioms AlgebraicCurve.omegaSpace_antitone
#print axioms AlgebraicCurve.omegaSpace_directed
#print axioms AlgebraicCurve.omegaSpace_le_weilDifferentialModule
#print axioms AlgebraicCurve.omegaSpace_vanishBdd
#print axioms AlgebraicCurve.omegaSpace_vanishGlobal
#print axioms AlgebraicCurve.one_mem_lSpace_zero
#print axioms AlgebraicCurve.Pic0.coe_degZeroSMulHom
#print axioms AlgebraicCurve.Pic0.mem_torsion
#print axioms AlgebraicCurve.Pic0.mk_add
#print axioms AlgebraicCurve.Pic0.mk_surjective
#print axioms AlgebraicCurve.Pic0.mk_zero
#print axioms AlgebraicCurve.Pic0.smul_mk
#print axioms AlgebraicCurve.Place._root_
#print axioms AlgebraicCurve.Place.adicValuation_algebraMap_le_one
#print axioms AlgebraicCurve.Place.adicValuation_coe
#print axioms AlgebraicCurve.Place.adicValuation_coe_eq_one_iff
#print axioms AlgebraicCurve.Place.adicValuation_coe_irreducible
#print axioms AlgebraicCurve.Place.adicValuation_eq_exp_neg_ord
#print axioms AlgebraicCurve.Place.adicValuation_le_exp_iff
#print axioms AlgebraicCurve.Place.adicValuation_le_one_iff
#print axioms AlgebraicCurve.Place.adicValuation_le_one_of_mem
#print axioms AlgebraicCurve.Place.adicValuation_ne_zero
#print axioms AlgebraicCurve.Place.coe_algebraMap
#print axioms AlgebraicCurve.Place.coe_smulRingEquiv_apply
#print axioms AlgebraicCurve.Place.deg_smul
#print axioms AlgebraicCurve.Place.exists_unit_mul_zpow
#print axioms AlgebraicCurve.Place.ext
#print axioms AlgebraicCurve.Place.heightOneSpectrum_asIdeal
#print axioms AlgebraicCurve.Place.isPrincipalIdealRing_valuationSubring
#print axioms AlgebraicCurve.Place.not_adicValuation_le_one_iff
#print axioms AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
#print axioms AlgebraicCurve.Place.ord_coe_irreducible
#print axioms AlgebraicCurve.Place.ord_coe_unit
#print axioms AlgebraicCurve.Place.ord_inv
#print axioms AlgebraicCurve.Place.ord_mul
#print axioms AlgebraicCurve.Place.ord_one
#print axioms AlgebraicCurve.Place.ord_smul
#print axioms AlgebraicCurve.Place.ord_unit_smul_zpow
#print axioms AlgebraicCurve.Place.ord_zero
#print axioms AlgebraicCurve.Place.ord_zpow
#print axioms AlgebraicCurve.Place.smul_toValuationSubring
#print axioms AlgebraicCurve.Place.toValuationSubring_injective
#print axioms AlgebraicCurve.repartitionsOf_mono
#print axioms AlgebraicCurve.residuePairing_apply_coe
#print axioms AlgebraicCurve.residuePairing_injective
#print axioms AlgebraicCurve.weilSmul_apply
#print axioms AlgebraicCurve.weilSmul_injective
#print axioms AlgebraicCurve.weilSmul_mem_omegaSpace_add
#print axioms AlgebraicCurve.weilSmul_mem_omegaSpace_of_mem_lSpace
#print axioms AlgebraicCurve.weilSmul_mul
#print axioms AlgebraicCurve.weilSmul_one
#print axioms CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_apply_coe
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_adeleBdd_mono
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_degree_add
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_degree_zero
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_ell_nonneg
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_isPrincipal_iff_mem
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_lSpace_mono
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_mem_degZero_iff
#print axioms LeanFormal.IUT.XiFPaper.AG_FLT_PromotionActual.promotion_place_deg_nonneg
#print axioms LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver_geometricallyConnected
#print axioms LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver_isProper
#print axioms LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver_isSmooth
#print axioms LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual.S3133CurveOver_relativeDimOne
#print axioms LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual.principalDivisor_coeff
#print axioms LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual.principalDivisor_mul
#print axioms LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual.principalDivisor_zero
#print axioms LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual.weilDivisor_add_apply
#print axioms LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual.weilDivisorSupport_zero
#print axioms LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual.agFunctionField_isFractionRing_of_isAffineOpen
#print axioms LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual.agGermToFunctionField_injective
#print axioms LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual.agOrderOfVanishing_germ_of_isUnit
#print axioms LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual.agOrderOfVanishing_mul
#print axioms LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual.agOrderOfVanishing_zero
#print axioms LeanFormal.IUT.XiFPaper.AG02GenusActual.S3133Genus_eq
#print axioms LeanFormal.IUT.XiFPaper.AG03bSectionsBasicActual.divisorSections_mono_coeff
#print axioms LeanFormal.IUT.XiFPaper.AG03bSectionsBasicActual.divisorSections_restrict
#print axioms LeanFormal.IUT.XiFPaper.AG03bSectionsBasicActual.unit_germ_mem_divisorSections_zero
#print axioms LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual.mem_divisorSections_iff
#print axioms LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual.smul_mem_divisorSections
#print axioms LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual.zero_mem_divisorSections
#print axioms LeanFormal.IUT.XiFPaper.AG04bResidueFieldActual.agResidueClass_apply
#print axioms LeanFormal.IUT.XiFPaper.AG04bResidueFieldActual.agSectionResidue_apply
#print axioms LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual.divisorSections_toWeilDivisor_eq
#print axioms LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual.toWeilDivisor_apply
#print axioms LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual.weilDivisorFinite_support_finite
#print axioms LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual.weilDivisorFiniteDegree_add
#print axioms LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual.weilDivisorFiniteDegree_zero
#print axioms LeanFormal.IUT.XiFPaper.AG94StepXIBindActual.S3137FLTAdaptationIds_length
#print axioms LeanFormal.IUT.XiFPaper.AG94StepXIBindActual.S3137StepXIAgIds_length
#print axioms LeanFormal.IUT.XiFPaper.AG94StepXIBindActual.S3137StepXIGenEllP3Ids_length
#print axioms LeanFormal.IUT.XiFPaper.AG94StepXIBindActual.S3137StepXIIndetIds_length
