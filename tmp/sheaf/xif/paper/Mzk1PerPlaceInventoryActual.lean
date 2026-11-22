/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A792 hull: per-place inequality inventory (reuse first, no duplicate proofs)

Inventory of existing green per-place / log-shell / q-side assets.  Statuses:
REUSE = already green and directly usable; PARTIAL = usable shape but needs a
missing instantiation; GAP = no existing proof. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInventoryActual

structure Row where
  item : String
  asset : String
  statement : String
  status : String
  deriving Repr, DecidableEq

def inventoryRows : List Row :=
  [ ⟨"A exponent", "IntegralLogShellSharpBounds.logShellPaperAExponent", "A/B paper exponents with floor/ceiling bounds", "REUSE"⟩
  , ⟨"B exponent", "IntegralLogShellSharpBounds.logShellPaperBExponent", "B exponent with padicValNat bounds", "REUSE"⟩
  , ⟨"B bound", "padicValNat_sub_div_le_logShellPaperBExponent", "padicVal <= B exponent", "REUSE"⟩
  , ⟨"small case", "logShellPaperAExponent_add_logShellPaperBExponent_eq_zero_of_small", "A+B = 0 for small p/e cases", "REUSE"⟩
  , ⟨"sum bound", "logShellPaperExponent_sum_mul_log_le_three_add_log", "(sum A+B) log p <= 3 + log p bound", "REUSE"⟩
  , ⟨"A minus 1/e", "logShellPaperAExponent_sub_inv_mul_log_le_four_div_mul_log / ..._le_two", "A - 1/e bounds", "REUSE"⟩
  , ⟨"B plus 1/e", "logShellPaperBExponent_add_inv_mul_log_le_one_add_log / ..._le_log_two_mul", "B + 1/e bounds", "REUSE"⟩
  , ⟨"probe", "IntegralLogShellSharpBoundsAxiomProbe", "trio axiom probes for all the above", "REUSE (GATE)"⟩
  , ⟨"StepV correction sum", "FinitePlaceStepVRealBound.stepVPaperCorrectionSum_le", "sum of A+B log p correction bound", "REUSE"⟩
  , ⟨"StepV log volume", "FinitePlaceStepVRealBound.stepVPaperLogVolumeBound", "log-volume Step V bound", "REUSE"⟩
  , ⟨"StepV assembly", "FinitePlaceStepVAssembly.arithmeticTupleStepVA/StepVB/EndpointExponent", "tuple-level Step V A/B and endpoint exponent", "REUSE (STRUCTURE)"⟩
  , ⟨"q norm exponent", "ArithmeticQPilotBaseChange.qNorm_eq_residueNormBase_zpow", "||q|| = residueNormBase^(-exponent)", "REUSE"⟩
  , ⟨"q log magnitude", "localLogMagnitude_eq_order_mul_log / _exponent_mul_log", "|log q| = order*log residueNormBase", "REUSE"⟩
  , ⟨"base power", "residueNormBase_eq_lower_pow / log_residueNormBase_eq_residueDegree_mul", "residueNormBase = lower^f; log = f*log lower", "REUSE"⟩
  , ⟨"global normalization", "ArithmeticQPilotGlobalNormalization.sum_fiberLogMagnitude_eq_integerRingRank_mul / selectedUpperMagnitude_eq_fieldDegree_mul", "global sums via [F:Q]", "REUSE"⟩
  , ⟨"local q log", "Mzk1QSideExplicitActual.qPilotLogVolumeReading_eq_neg_order_mul_log", "q reading = -(order*log residueNormBase)", "REUSE"⟩
  , ⟨"C3 block measure", "Mzk1C3BlockMeasureActual.c3Tensor_measure_pow_prime_smul / c3TensorBlockDimension_eq_prod", "p-power scaling of C3 block", "REUSE"⟩
  , ⟨"positive theta hull volume", "GlobalPositiveThetaHullLogVolumeActual.thetaPositiveLogVolumeAt_eq / globalThetaHullPositiveLogVolume_eq", "positive θ hull log-volume", "REUSE (POSITIVE CASE)"⟩
  , ⟨"paper mu formula", "ROUTES §6.1: log mu = (1+[p=2]-1/e-r/n) log p", "paper normalization of shell volume", "DEF (Mzk1DiffNonnegActual.paperShellLogMu)"⟩
  , ⟨"diff formula", "Mzk1DiffNonnegActual.diffV_nonneg_iff_Dbar", "diff>=0 iff logIdx <= 2l log mu", "REUSE + CORRECTION"⟩
  , ⟨"negative instance", "Mzk1DiffNonnegActual.diffV_negative_instance_neg", "diff_v>=0 false in Qp(zeta_p) model (p=5,l=1/2)", "COUNTEREXAMPLE"⟩
  , ⟨"per-place reduction", "Mzk1PerPlaceBoundHullActual.perPlace_inequality_of_mu_lower_diff", "L<=log mu and qcoef<=L+(1-1/2l)logIdx => qcoef<=logIdx+diff", "REUSE (ARITHMETIC)"⟩
  , ⟨"per-place target", "A_v <= Lbar_v + Dbar_v, equivalently logIdx_v <= 2l logMu_v", "correct per-place inequality", "GAP: arithmetic instantiation of qcoef=(f/[F:Q])logp/(2l) and A/B/e,r,n bounds"⟩
  , ⟨"global gluing", "sum over bad places of the per-place target", "A <= Lbar + Dbar", "GAP: depends on per-place target + arch/torsion terms"⟩
  , ⟨"scope", "", "no new proof duplicated; this file is inventory only", "INTEGRITY"⟩
  ]

end LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInventoryActual

end