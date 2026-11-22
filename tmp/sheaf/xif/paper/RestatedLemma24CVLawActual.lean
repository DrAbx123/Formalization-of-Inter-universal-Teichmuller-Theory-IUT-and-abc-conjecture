import Mathlib
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma22FullShapeHelpersActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.RestatedLemma24CVLawActual

open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22FullShapeHelpersActual

/-- The C-point critical-value set agrees with the ported TauCeti criticalValues over C. -/
theorem s3135_criticalValuesOverC_eq (q : Polynomial ℚ) :
    criticalValuesOverC q = q.criticalValues ℂ := by
  ext c
  constructor
  · rintro ⟨z, hdeg, hz, rfl⟩
    have hder : Polynomial.derivative q ≠ 0 := by
      intro h
      exact hdeg ((Polynomial.derivative_eq_zero).mp h)
    refine ⟨z, (Polynomial.mem_rootSet_of_ne (p := Polynomial.derivative q) hder).mpr hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hder : Polynomial.derivative q ≠ 0 := by
      intro h
      rw [h] at hz
      simp [Polynomial.rootSet] at hz
    have hz' : Polynomial.aeval z (Polynomial.derivative q) = 0 :=
      (Polynomial.mem_rootSet_of_ne (p := Polynomial.derivative q) hder).mp hz
    refine ⟨z, ?_, hz', rfl⟩
    intro hzdeg
    exact hder ((Polynomial.derivative_eq_zero).mpr hzdeg)

/-- **CV composition law PROVED** from the ported TauCeti theorem (via hull's re-export):
critical values of r.comp q are contained in the image of q's critical values under r
together with r's critical values. -/
theorem s3135_CVCompositionLawStatement_proved : CVCompositionLawStatement := by
  intro q r
  have h := critValues_comp_subset r q
  simpa [s3135_criticalValuesOverC_eq] using h

/-- **Special-set preservation PROVED**: if r maps 0 and 1 into {0,1}, then it maps the
Belyi special set {0,1} into itself (trivial case analysis). -/
theorem s3135_SpecialSetPreservationStatement_proved : SpecialSetPreservationStatement := by
  intro r h0 h1 c hc
  rcases hc with rfl | rfl
  · exact h0
  · exact h1

/-- Combined CV compatibility for the restated 2.4 target (matches stepxi's
Mzk1Lemma22CVCompat): composition law and special-set preservation, both PROVED. -/
theorem s3135_CVCompat_proved :
    CVCompositionLawStatement ∧ SpecialSetPreservationStatement :=
  ⟨s3135_CVCompositionLawStatement_proved, s3135_SpecialSetPreservationStatement_proved⟩

/-- Status: CV composition law and special-set preservation for the restated 2.4 target
are PROVED (composition law from ported TauCeti criticalValues_comp_subset via hull's
FullShapeHelpers re-export; special-set preservation by case analysis).  These are the
CV-accounting inputs of the corrected induction; no paper closure claimed (binding HOLD). -/
def RestatedLemma24CVLawStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.restated-cv-law"
    source := "ported TauCeti CriticalValues (criticalValues_comp_subset); hull Mzk1Lemma22FullShapeHelpersActual; Lead A280 restatement"
    status := Audit.VerificationStatus.interface
    note := "PROVED: s3135_criticalValuesOverC_eq (our C-point CV equals ported TauCeti q.criticalValues C); s3135_CVCompositionLawStatement_proved (CV(r.comp q) subset (aeval . r) '' CV q union CV r, from critValues_comp_subset r q); s3135_SpecialSetPreservationStatement_proved (0,1 images in {0,1} imply special-set preservation); combined s3135_CVCompat_proved = CVCompositionLawStatement AND SpecialSetPreservationStatement (same pair as stepxi Mzk1Lemma22CVCompat). These supply the CV accounting inputs consumed by RestatedLemma24InductionActual.s3135_CVInvariant_comp. No paper closure claimed; binding HOLD; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.restated-induction" ]
    sorryItems := [] }

#check s3135_CVCompositionLawStatement_proved
#check s3135_CVCompat_proved
end LeanFormal.IUT.XiFPaper.RestatedLemma24CVLawActual
end