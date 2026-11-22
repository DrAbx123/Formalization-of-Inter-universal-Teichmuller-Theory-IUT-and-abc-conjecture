/-
  Owned metadata probe for the actual StepXI/ABC boundary audit (v2).
  Contract: actual_stepxi_abc_boundary-v1
  Run: core-construction-map-20261014
  Owner: dsh_stepxi_boundary_owner, generation 2

  Scope: public imports, #check of public types/signatures, #print axioms, and
  module/signature metadata only. No implementation bodies are printed.
  Note: LeanFormal.IUT.ABCBridge.UnprovedTarget has no .olean, so it is not
  imported here; its single declaration is reported from the frozen source text.
-/

import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Statement

namespace CoreConstructionMapAudit

-- Actual ABC arithmetic target and its supporting definitions.
#check LeanFormal.IUT.ABCConjecture
#check LeanFormal.IUT.ABCInequality
#check LeanFormal.IUT.IsABCTriple
#check LeanFormal.IUT.radical

-- Locally re-exported radical lemmas and definitional unfolding lemma.
#check LeanFormal.IUT.radical_zero
#check LeanFormal.IUT.radical_pos
#check LeanFormal.IUT.radical_dvd_self
#check LeanFormal.IUT.radical_eq_one_iff
#check LeanFormal.IUT.abcInequality_is_explicit

-- Axiom footprint of the proved Statement.lean declarations.
#print axioms LeanFormal.IUT.radical_zero
#print axioms LeanFormal.IUT.radical_pos
#print axioms LeanFormal.IUT.radical_dvd_self
#print axioms LeanFormal.IUT.radical_eq_one_iff
#print axioms LeanFormal.IUT.abcInequality_is_explicit

-- Audit obligation records (metadata only).
#check LeanFormal.IUT.Audit.ipl
#check LeanFormal.IUT.Audit.she
#check LeanFormal.IUT.Audit.apt
#check LeanFormal.IUT.Audit.cor312ToABCBridge

-- Carrier / external definitions used by Statement.lean.
#check LeanFormal.IUT.natRadical
#check LeanFormal.IUT.PrimitiveAdditiveTriple
#check LeanFormal.IUT.Audit.Obligation
#check LeanFormal.IUT.Audit.VerificationStatus

end CoreConstructionMapAudit
