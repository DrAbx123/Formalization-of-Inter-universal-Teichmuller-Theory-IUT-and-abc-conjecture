import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# ShehddLogShellIdentificationConsumerActualAdapted — log-shell invariant image identification consumer

STEP 0 prior-art (reuse only; A475 search: log-shell bridge assets found):
* SourceLogShellAbsTopIIIBridge.lean: SourceLogShellInvariantImageIdentification
  (D.unitLayer = D.preLogShell), equivalence shapes
  (invariantImageIdentification_iff_unitLayer_subset / _iff_forall_log_mem /
   _iff_invariants_eq_top_of_injective), conservative consequence
  codomainKummerContained_of_invariantImageIdentification, logShell = invScaledUnitLayer,
  kummerImages_mem_logShell, toNonarchimedeanUpperSemi assembly.

This file packages the bridge card's consequences as one consumer for the [AbsTopIII]
log-shell identification layer.  No new assumptions, no sorry/axiom; the source arithmetic
fact remains the named card (file header 缩减点).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddLogShellIdentificationConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** the invariant-image identification card gives the equality, the
one-sided containment, codomain Kummer containment, the `logShell = invScaledUnitLayer`
form, and the Kummer-image containment rows. -/
theorem logShellIdentification_consumer (D : SourceLogShellDatum)
    (h : SourceLogShellInvariantImageIdentification D) :
    D.unitLayer = D.preLogShell ∧
      D.unitLayer ⊆ D.preLogShell ∧
        D.codomainKummerContained ∧
          D.logShell = D.invScaledUnitLayer ∧
            (∀ u ∈ D.invariants, (D.logMap u).toAdd ∈ D.logShell) ∧
              (∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell) ∧
                (∀ u : D.Units, (D.logMap u).toAdd ∈ D.preLogShell) :=
  ⟨h,
    (SourceLogShellDatum.invariantImageIdentification_iff_unitLayer_subset D).mp h,
    SourceLogShellDatum.codomainKummerContained_of_invariantImageIdentification D h,
    SourceLogShellDatum.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification D h,
    (SourceLogShellDatum.kummerImages_mem_logShell_of_invariantImageIdentification D h).1,
    (SourceLogShellDatum.kummerImages_mem_logShell_of_invariantImageIdentification D h).2,
    (SourceLogShellDatum.invariantImageIdentification_iff_forall_log_mem D).mp h⟩

/-- **PROVED consumer:** the identification card assembles the nonarchimedean
log-Kummer upper-semi structure. -/
theorem logShellIdentification_upperSemi (D : SourceLogShellDatum)
    (h : SourceLogShellInvariantImageIdentification D) :
    NonarchimedeanLogKummerUpperSemi :=
  SourceLogShellDatum.toNonarchimedeanUpperSemi_of_invariantImageIdentification D h

/-- Row record: reused bridge-card laws vs the consumer interface. -/
def logShellIdentificationRows : List (String × String × String) :=
  [ ("bridge card definition D.unitLayer = D.preLogShell", "REUSED DEF", "SourceLogShellAbsTopIIIBridge.SourceLogShellInvariantImageIdentification")
  , ("equivalence shapes (subset / forall-log-mem / invariants=top under injectivity)", "REUSED PROVED", "invariantImageIdentification_iff_*")
  , ("conservative consequence + logShell = invScaledUnitLayer", "REUSED PROVED", "codomainKummerContained_of_... / logShell_eq_invScaledUnitLayer_of_...")
  , ("Kummer image containment rows + upper-semi assembly", "REUSED PROVED", "kummerImages_mem_logShell_of_... / toNonarchimedeanUpperSemi_of_...")
  , ("consumer bundle", "COMPOSED PROVED", "logShellIdentification_consumer, logShellIdentification_upperSemi")
  , ("source arithmetic fact (O^×)^pf^Π = O^× + log transfer", "NAMED (file header 缩减点)", "bridge card replaces it with explicit condition") ]

theorem logShellIdentificationRows_length : logShellIdentificationRows.length = 6 := rfl

#check logShellIdentification_consumer
#check logShellIdentification_upperSemi
#check logShellIdentificationRows_length

end LeanFormal.IUT.XiFPaper.ShehddLogShellIdentificationConsumerActualAdapted
end
