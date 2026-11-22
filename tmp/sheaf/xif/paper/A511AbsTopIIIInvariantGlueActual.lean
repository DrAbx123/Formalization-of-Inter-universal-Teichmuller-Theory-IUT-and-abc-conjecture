/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-! # A511 glue: invariant-image card objects for the AbsTopIII log-shell bridge -/

noncomputable section

namespace LeanFormal.IUT.Objects.AbsTopIII

open LeanFormal.IUT

/-- An invariant-image card object: a source log-shell datum together with the bridge card
`unitLayer = preLogShell`. -/
structure InvariantImageObject where
  /-- The source log-shell datum. -/
  datum : SourceLogShellDatum
  /-- The bridge identification card. -/
  card : SourceLogShellInvariantImageIdentification datum

/-- The card implies the unit-layer containment (consumer of the bridge iff). -/
theorem InvariantImageObject.unitLayer_subset (D : InvariantImageObject) :
    D.datum.unitLayer ⊆ D.datum.preLogShell :=
  (SourceLogShellDatum.invariantImageIdentification_iff_unitLayer_subset D.datum).mp D.card

/-- The card implies codomain Kummer containment (the main conservative consequence). -/
theorem InvariantImageObject.codomainKummerContained (D : InvariantImageObject) :
    D.datum.codomainKummerContained :=
  SourceLogShellDatum.codomainKummerContained_of_invariantImageIdentification D.datum D.card

/-- The pointwise log-membership form of the card. -/
theorem InvariantImageObject.forall_log_mem (D : InvariantImageObject) :
    ∀ u : D.datum.Units, (D.datum.logMap u).toAdd ∈ D.datum.preLogShell :=
  (SourceLogShellDatum.invariantImageIdentification_iff_forall_log_mem D.datum).mp D.card

end LeanFormal.IUT.Objects.AbsTopIII
