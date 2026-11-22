import tmp.sheaf.n8.closure.EtaRemainingDonorsAssembly
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D5D8Root

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# O1 source cards: orbicurve, sections, cusp, compatibility

Exact O1 card targets and the one actual conditional section constructor.

Actual:
- D7a place-section layer is constructed for every arithmetic input by
  SourceValuationSectionLayer.canonical.
- Given the D7b local-group supply, the full SourceSectionClause is assembled
  by the production d7SectionLayerBridge.  This is the only actual clause
  construction available among the O1 cards.

Exact gaps (no arbitrary witness, no degenerate clause):
- orbicurve: needs actual hyperbolic orbicurves X_K/C_K and certified etale
  fundamental groups; the production orbicurve file explicitly refuses to
  manufacture SourceOrbicurveClause from degenerate terminal stack data.
- sections: D7b local-group carriers/pointwise bijections/place data are the
  explicit missing supply; native data supplies only D7a.
- cusp: needs the selected cusp datum (nonzero quotient, canonical generator,
  sign ambiguity) and the Real epsilon/cuspScale source card; no native field.
- compatibility: the five arithmetic (Prop, proof) pairs remain explicit source
  fields; NativeArithmeticCompatibilityTarget is not derived from native S.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.EtaRemainingDonorsAssembly
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

namespace LeanFormal.IUT.N8Closure.O1SourceCardsActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- O1 card bundle: the four remaining source cards, exact clause types. -/
structure O1SourceCards (X : N8NativeInput l) where
  /-- O1 card: source orbicurve clause. -/
  orbicurve : SourceOrbicurveClause.{0, 0, 0}
  /-- O1 card: source section clause. -/
  sections : SourceSectionClause.{0, 0, 0}
  /-- O1 card: source cusp clause. -/
  cusp : SourceCuspClause
  /-- O1 card: five arithmetic compatibility slots. -/
  compatibility : NativeArithmeticCompatibilityTarget

def O1SourceCardsTarget : Prop :=
  Nonempty (O1SourceCards (l := l) X)

def O1OrbicurveCardTarget : Prop :=
  Nonempty (SourceOrbicurveClause.{0, 0, 0})

def O1SectionsCardTarget : Prop :=
  Nonempty (SourceSectionClause.{0, 0, 0})

def O1CuspCardTarget : Prop :=
  Nonempty (SourceCuspClause)

def O1CompatibilityCardTarget : Prop :=
  Nonempty (NativeArithmeticCompatibilityTarget)

theorem o1SourceCardsTarget_iff_components :
    O1SourceCardsTarget (X := X) ↔
      O1OrbicurveCardTarget ∧ O1SectionsCardTarget ∧
        O1CuspCardTarget ∧ O1CompatibilityCardTarget := by
  constructor
  · rintro ⟨C⟩
    exact ⟨⟨C.orbicurve⟩, ⟨C.sections⟩, ⟨C.cusp⟩, ⟨C.compatibility⟩⟩
  · rintro ⟨⟨O⟩, ⟨S⟩, ⟨Cu⟩, ⟨K⟩⟩
    exact ⟨O, S, Cu, K⟩

/-- Actual D7a place-section layer for the native arithmetic input. -/
noncomputable def o1CanonicalSectionLayer :
    SourceValuationSectionLayer X.S.arithmetic :=
  SourceValuationSectionLayer.canonical X.S.arithmetic

/-- Actual conditional assembly of SourceSectionClause from the D7b local-group
supply, using the production d7SectionLayerBridge.  This is the only actual
card construction in this file; the supply itself is the exact gap. -/
noncomputable def o1SectionClauseOfLocalGroups
    (G : D7LocalGroupSectionSupply.{0, 0}
      (SourceValuationSectionLayer.canonical X.S.arithmetic)) :
    SourceSectionClause.{0, 0, 0} :=
  d7SectionLayerBridge
    (SourceValuationSectionLayer.canonical X.S.arithmetic) G

theorem o1SectionsCardTarget_of_localGroups
    (G : D7LocalGroupSectionSupply.{0, 0}
      (SourceValuationSectionLayer.canonical X.S.arithmetic)) :
    O1SectionsCardTarget :=
  ⟨o1SectionClauseOfLocalGroups (X := X) G⟩

/-- Exact O1 gap bundle.  No construction of the clauses is asserted. -/
structure O1SourceCardsGap (X : N8NativeInput l) where
  orbicurve_missing : O1OrbicurveCardTarget
  sections_localGroups_missing :
    D7LocalGroupSectionSupply.{0, 0}
      (SourceValuationSectionLayer.canonical X.S.arithmetic)
  cusp_missing : O1CuspCardTarget
  compatibility_missing : O1CompatibilityCardTarget

def O1CardsUnconstructed : Prop :=
  ¬ O1SourceCardsTarget (X := X)

end LeanFormal.IUT.N8Closure.O1SourceCardsActual

end