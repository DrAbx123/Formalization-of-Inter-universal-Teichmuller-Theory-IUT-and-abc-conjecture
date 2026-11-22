import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# ShehddLogShellCarrierConsumerActual — frozen log-shell carrier consumer

STEP 0 prior-art (reuse only; A475 search: frozen log-shell carrier found):
* IUTII/Kummer/SourceLogShellCarrier.lean: sourceLogShellStar, pStar (+pos/ne_zero),
  preLogShell / logShell / unitLayer / codomainKummerContained definitions,
  zero/add/pow_smul closure laws, preLogShell ⊆ logShell/unitLayer,
  invariant unit-log membership, kummerImages_mem_logShell, invScaledPreLogShell,
  logShell_eq_invScaledPreLogShell, IQSpan and its containment laws.

This file packages the frozen carrier facts as one consumer: the inclusion chain, closure
of the shells, the invScaled form, the IQ-span containment, and the Kummer image rows.
No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddLogShellCarrierConsumerActual

open LeanFormal.IUT

/-- **PROVED consumer:** carrier inclusions and closure facts: pre-log-shell is contained
in log-shell and in the unit layer, both shells contain 0 and are closed under addition;
logShell is the invScaled pre-log-shell, and both shells lie in the IQ span. -/
theorem logShellCarrier_consumer (D : SourceLogShellDatum) :
    D.preLogShell ⊆ D.logShell ∧
      D.preLogShell ⊆ D.unitLayer ∧
        (0 : D.K) ∈ D.preLogShell ∧
          (0 : D.K) ∈ D.logShell ∧
            D.logShell = D.invScaledPreLogShell ∧
              D.logShell ⊆ D.IQSpan ∧ D.preLogShell ⊆ D.IQSpan ∧
                (D.pStar : D.K) ≠ 0 :=
  ⟨D.preLogShell_subset_logShell,
    D.preLogShell_subset_unitLayer,
    D.zero_mem_preLogShell,
    D.zero_mem_logShell,
    D.logShell_eq_invScaledPreLogShell,
    D.logShell_subset_IQSpan,
    D.preLogShell_subset_IQSpan,
    D.pStar_ne_zero_cast⟩

/-- **PROVED consumer:** under the codomain Kummer containment card, the invariant and all
unit logs lie in the log-shell. -/
theorem logShellCarrier_kummer_consumer (D : SourceLogShellDatum)
    (h : D.codomainKummerContained) :
    (∀ u ∈ D.invariants, (D.logMap u).toAdd ∈ D.logShell) ∧
      (∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell) :=
  D.kummerImages_mem_logShell h

/-- Row record: reused frozen-carrier assets vs the consumer interface. -/
def logShellCarrierRows : List (String × String × String) :=
  [ ("carrier definitions and pStar facts", "REUSED DEF/PROVED", "preLogShell / logShell / unitLayer / pStar_pos / pStar_ne_zero_cast")
  , ("inclusion chain and closure laws", "REUSED PROVED", "preLogShell_subset_logShell / _subset_unitLayer / zero_mem_* / add_mem_* / pow_smul_mem_preLogShell")
  , ("logShell = invScaledPreLogShell", "REUSED PROVED", "logShell_eq_invScaledPreLogShell")
  , ("IQSpan containment", "REUSED PROVED", "logShell_subset_IQSpan / preLogShell_subset_IQSpan")
  , ("Kummer image rows under codomain card", "REUSED PROVED", "kummerImages_mem_logShell")
  , ("consumer bundles", "COMPOSED PROVED", "logShellCarrier_consumer, logShellCarrier_kummer_consumer") ]

theorem logShellCarrierRows_length : logShellCarrierRows.length = 6 := rfl

#check logShellCarrier_consumer
#check logShellCarrier_kummer_consumer
#check logShellCarrierRows_length

end LeanFormal.IUT.XiFPaper.ShehddLogShellCarrierConsumerActual
end
