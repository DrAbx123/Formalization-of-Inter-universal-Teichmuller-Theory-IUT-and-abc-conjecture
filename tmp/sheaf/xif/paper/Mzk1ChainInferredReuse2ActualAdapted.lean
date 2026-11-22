import LeanFormal/IUT/ABCBridge/Geometry/FreyOddReduction
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardHullRealGeometryReduction
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply
import LeanFormal/IUT/IUTII/Kummer/AbsoluteKummerInjection
import LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2KummerPrimeLift
import LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface
import LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierReductions

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ChainInferredReuse2ActualAdapted (adapted copy, A475 reuse) — A475 donor aliases/chains (Frey/hull/AMPL/Kummer/bridge)

All entries are inferred-type re-exports/compositions of existing declarations:
* Frey p-adic model: `FreyOddReduction.lean:30/37/45`;
* H5 hull engine: `CardHullRealGeometryReduction.lean:94/108/278/297`;
* AMPL theta-bound supply: `CardAMPLThetaBoundSupply.lean:94/101/109`;
* absolute Kummer map: `AbsoluteKummerInjection.lean:119`;
* K1K2 labelled Kummer iso: `SourceK1K2KummerPrimeLift.lean:131`;
* Cor312 bridge height bound: `Cor312ToABCBridgeInterface.lean:cor312ToABCBridge_heightBound`;
* ABC frontier real-line chain: `ABCFrontierReductions.lean:301/256` + `ABCFrontier.reduce_realLine`.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainInferredReuse2ActualAdapted

open LeanFormal.IUT

/-- Frey p-adic integral model equals the base change (donor alias). -/
theorem chain_frey_eq_int_map := @freyPadicIntegralModel_eq_int_map

/-- Frey p-adic model base-change law (donor alias). -/
theorem chain_frey_baseChange := @freyPadicIntegralModel_baseChange

/-- Frey p-adic curve integrality (donor alias). -/
theorem chain_frey_integral := @freyPadicCurve_isIntegral

/-- H5 scaling units inside holomorphic hull (donor alias). -/
theorem chain_hull_scaling_subset := @sourceScalingUnits_subset_sourceHolomorphicHull

/-- H5 holomorphic hull equals closure (donor alias). -/
theorem chain_hull_eq_closure := @sourceHolomorphicHull_eq_closure

/-- H5 hull<=image conditional candidate criterion (donor alias). -/
theorem chain_hull_candidate_le := @sourceHullVolume_le_imageVolume_of_candidate

/-- H5 local log-degree nonpositive on the hull (donor alias). -/
theorem chain_hull_local_logDegree := @sourceLocalLogDegree_le_zero_of_mem_sourceHolomorphicHull

/-- AMPL theta-bound realVolume_le (donor alias). -/
theorem chain_ampl_realVolume := @CardAMPLThetaBoundSupply.realVolume_le

/-- AMPL theta-bound ofReal_le_theta (donor alias). -/
theorem chain_ampl_ofReal_le := @CardAMPLThetaBoundSupply.ofReal_le_theta_of_imageSet_lower

/-- AMPL theta-bound exists hull eq ofReal (donor alias). -/
theorem chain_ampl_exists_hull_eq := @CardAMPLThetaBoundSupply.exists_hull_eq_ofReal

/-- Absolute Kummer map = 1 characterization (donor alias). -/
theorem chain_absKummer_one_iff := @absoluteKummerMap_eq_one_iff

/-- Labelled Kummer iso nonempty (donor alias). -/
theorem chain_labelledKummerIso_nonempty := @labelledKummerIso_nonempty_of_localKummerRootRealizationFor_prime

/-- Cor312 bridge height bound (donor alias). -/
theorem chain_bridge_heightBound := @cor312ToABCBridge_heightBound

/-- Real-line frontier -> ABC (two-donor chain). -/
theorem chain_realLine_abc :=
  fun h => abcConjecture_of_frontier (ABCFrontier.reduce_realLine h)

def chainInferred2Rows : List (String × String × String) :=
  [ ("Frey model", "REUSED donor", "chain_frey_eq_int_map/baseChange/integral"),
    ("H5 hull engine", "REUSED donor", "chain_hull_scaling_subset/eq_closure/candidate_le/local_logDegree"),
    ("AMPL theta bound", "REUSED donor", "chain_ampl_realVolume/ofReal_le/exists_hull_eq"),
    ("absolute Kummer", "REUSED donor", "chain_absKummer_one_iff"),
    ("K1K2 Kummer iso", "REUSED donor", "chain_labelledKummerIso_nonempty"),
    ("Cor312 bridge height bound", "REUSED donor", "chain_bridge_heightBound"),
    ("real-line frontier -> ABC", "CHAIN PROVED", "chain_realLine_abc") ]

theorem chainInferred2Rows_length : chainInferred2Rows.length = 7 := rfl

#check chain_hull_candidate_le
#check chainInferred2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1ChainInferredReuse2ActualAdapted
end