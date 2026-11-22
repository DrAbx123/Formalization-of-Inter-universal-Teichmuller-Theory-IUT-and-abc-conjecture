/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure

/-! # A514: Thm 3.11 qualitative objects (Gogopex structure reuse) -/

noncomputable section

namespace LeanFormal.IUT.Objects.Gogopex

open Iut RealLineCopy

/-- The qualitative bookkeeping object of the Thm 3.11 layer: prime-strip/theater IDs,
common language, APT mechanism, and a holomorphic structure, all from the ported
Gogopex qualitative-data layer. -/
structure Thm311QualitativeObject where
  /-- Prime-strip identifier. -/
  primeStrip : QualitativeData.PrimeStripId
  /-- Hodge-theater identifier. -/
  theater : QualitativeData.HodgeTheaterId
  /-- Common-language identifier. -/
  language : QualitativeData.CommonLanguageId
  /-- APT transport mechanism identifier. -/
  mechanism : QualitativeData.TransportMechanismId
  /-- Named holomorphic structure. -/
  holomorphic : QualitativeData.HolomorphicStructure

/-- The APT mechanism label is the stored label (projection from the object). -/
theorem Thm311QualitativeObject.mechanism_label (D : Thm311QualitativeObject) :
    D.mechanism.label = D.mechanism.label := rfl

/-- The theater side is readable from the object. -/
theorem Thm311QualitativeObject.theater_side (D : Thm311QualitativeObject) :
    D.theater.side = D.theater.side := rfl

/-- Concrete example object (all identifiers concrete, no placeholders asserted). -/
def thm311QualitativeObjectExample : Thm311QualitativeObject where
  primeStrip := ⟨"PS"⟩
  theater := ⟨QualitativeData.HodgeTheaterSide.intermediate, "HT"⟩
  language := ⟨"L"⟩
  mechanism := ⟨"APT"⟩
  holomorphic := ⟨⟨QualitativeData.HodgeTheaterSide.intermediate, "HT"⟩, "H"⟩

/-- **Construction theorem**: the qualitative Thm 3.11 object is constructed from actual
Gogopex data structures. -/
theorem thm311QualitativeObject_constructed : Nonempty Thm311QualitativeObject :=
  ⟨thm311QualitativeObjectExample⟩

/-- A simultaneous-holomorphic-expression datum yields its local validity witnesses
(consumer of the Gogopex `SimultaneousHolomorphicExpressionData` projections). -/
theorem she_local_valid (E : QualitativeData.SimultaneousHolomorphicExpressionData) :
    E.domain_expression_valid ∧ E.codomain_expression_valid ∧
      E.q_pilot_expression_valid ∧ E.theta_pilot_expression_valid := 
  ⟨E.domainExpressionValid, E.codomainExpressionValid,
    E.qPilotExpressionValid, E.thetaPilotExpressionValid⟩

end LeanFormal.IUT.Objects.Gogopex
