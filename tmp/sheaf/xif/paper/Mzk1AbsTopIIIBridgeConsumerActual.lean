/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-! # AbsTopIII 5.8/5.5: consumers combining invariant-image identification cards -/

namespace LeanFormal.IUT

namespace SourceLogShellDatum

theorem consumer_forall_log_mem_iff_unitLayer_subset (D : SourceLogShellDatum) :
    (∀ u : D.Units, (D.logMap u).toAdd ∈ D.preLogShell) ↔
      D.unitLayer ⊆ D.preLogShell := by
  rw [← invariantImageIdentification_iff_forall_log_mem,
    invariantImageIdentification_iff_unitLayer_subset]

theorem consumer_codomainKummerContained_of_forall_log_mem (D : SourceLogShellDatum)
    (h : ∀ u : D.Units, (D.logMap u).toAdd ∈ D.preLogShell) :
    D.codomainKummerContained := by
  apply codomainKummerContained_of_invariantImageIdentification
  exact (invariantImageIdentification_iff_forall_log_mem D).mpr h

theorem consumer_codomainKummerContained_of_invariants_eq_top (D : SourceLogShellDatum)
    (h : D.invariants = ⊤) : D.codomainKummerContained :=
  codomainKummerContained_of_invariantImageIdentification D
    (invariantImageIdentification_of_invariants_eq_top D h)

theorem consumer_invariantImageIdentification_of_unitLayer_subset (D : SourceLogShellDatum)
    (h : D.unitLayer ⊆ D.preLogShell) :
    SourceLogShellInvariantImageIdentification D :=
  (invariantImageIdentification_iff_unitLayer_subset D).mpr h

end SourceLogShellDatum

end LeanFormal.IUT
