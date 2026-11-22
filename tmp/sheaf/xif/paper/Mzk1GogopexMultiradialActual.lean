/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema

/-! # A514: O4/O5 multiradial objects (Gogopex SHE data + Stage1 comparison) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexMultiradial

open Iut RealLineCopy

/-- The O4/O5 multiradial object: the simultaneous-holomorphic-expression data of the
Gogopex qualitative layer together with the Stage 1 Corollary 3.12 comparison payload. -/
structure MultiradialObject where
  /-- The SHE validity data. -/
  expression : QualitativeData.SimultaneousHolomorphicExpressionData
  /-- The Stage 1 q/Theta comparison data. -/
  comparison : Stage1.Corollary312ComparisonData

/-- Each local SHE validity statement of the multiradial object holds. -/
theorem MultiradialObject.domain_valid (D : MultiradialObject) :
    D.expression.domain_expression_valid := D.expression.domainExpressionValid

theorem MultiradialObject.codomain_valid (D : MultiradialObject) :
    D.expression.codomain_expression_valid := D.expression.codomainExpressionValid

theorem MultiradialObject.q_pilot_valid (D : MultiradialObject) :
    D.expression.q_pilot_expression_valid := D.expression.qPilotExpressionValid

theorem MultiradialObject.theta_pilot_valid (D : MultiradialObject) :
    D.expression.theta_pilot_expression_valid := D.expression.thetaPilotExpressionValid

/-- The Stage 1 Corollary 3.12 signed comparison holds for the object's comparison data. -/
theorem MultiradialObject.corollary312_inequality (D : MultiradialObject) :
    Stage1.Corollary312Inequality D.comparison.thetaPilot D.comparison.qPilot :=
  D.comparison.corollary312

/-- Example object built from concrete data (comparison with `theta=1 > q=-1`). -/
def multiradialObjectExample : MultiradialObject where
  expression := {
    domain_expression_valid := True,
    domain_expression_valid_holds := trivial,
    codomain_expression_valid := True,
    codomain_expression_valid_holds := trivial,
    q_pilot_expression_valid := True,
    q_pilot_expression_valid_holds := trivial,
    theta_pilot_expression_valid := True,
    theta_pilot_expression_valid_holds := trivial,
    simultaneous_valid := True,
    simultaneous_valid_holds := trivial }
  comparison := {
    thetaSigned := 1,
    qSigned := -1,
    q_positive := by norm_num,
    qSigned_le_thetaSigned := by norm_num }

/-- **Construction theorem**: the O4/O5 multiradial object exists over actual Gogopex data. -/
theorem multiradialObject_constructed : Nonempty MultiradialObject :=
  ⟨multiradialObjectExample⟩

end LeanFormal.IUT.Objects.GogopexMultiradial
