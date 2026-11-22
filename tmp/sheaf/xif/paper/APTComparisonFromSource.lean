import tmp.sheaf.xif.paper.SHEAlgorithmFromSource
import tmp.sheaf.xif.paper.SHEOutputAlignmentActual
import tmp.sheaf.xif.paper.SHELandingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT

/-! # CONDITIONAL STATUS (xi-f)

Conditional on SHELandingForProcessionChoice. The actual two-column comparison is constructed; the SHE landing over ProcessionChoice is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual non-reflexive TwoActionEquivalence for APT

The production finite-kernel wiring constructs the non-reflexive adjacent-
column comparison `finiteKernelTwoColumnComparison`: its output equivalence is
the (Ind2) translation `ind2KernelPerm`, its (Ind1) group equivalence is the
identity, and the preservation of both actions is proved from the production
commutation lemmas. This file instantiates that actual comparison and wires it
into the reduced APT transport/statement whenever the SHE landing for the
actual ProcessionChoice output is supplied.

The comparison itself is actual; the missing field for `SourceAPTStatement`
is exactly the SHE landing for `ProcessionChoice l`, not any action
compatibility. No toy/True/PUnit/sorry/axiom. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.APTComparisonFromSource

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource
open LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual
open LeanFormal.IUT.SourceMultiradialPresentationWiring
open LeanFormal.IUT.ConcreteFiniteTheorem311

universe ua upi umon ui

variable {k : Type} [Field k] [NumberField k] {l : PrimeGeFive}
variable {n : Int} {shift : finiteLabel l} {source : ProcessionChoice l}
variable {I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k)}

/-- The actual non-reflexive adjacent-column comparison from the production
 finite-kernel wiring. Its preservation fields are proved, not assumed. -/
def actualTwoColumnComparison
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l) (source : ProcessionChoice l) :
    SourceTheorem311TwoActionEquivalence
      (finiteKernelSourceAlgorithm l I n (finiteKernelComparisonInput l source))
      (finiteKernelSourceAlgorithm l I (n + 1)
        (finiteKernelComparisonInput l (ProcessionChoice.ind2Act shift source))) :=
  finiteKernelTwoColumnComparison l I n shift source

/-- The actual comparison's output equivalence is the non-identity (Ind2)
 translation at a nonzero shift. -/
theorem actualTwoColumnComparison_nontrivial
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l) (hshift : shift ≠ 0)
    (source : ProcessionChoice l) :
    (actualTwoColumnComparison I n shift source).outputEquiv
      ProcessionChoice.base ≠ ProcessionChoice.base :=
  finiteKernelTwoColumnComparison_nontrivial l I n shift hshift source

/-- The actual comparison's output equivalence is not the identity. -/
theorem actualTwoColumnComparison_outputEquiv_ne_refl
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l) (hshift : shift ≠ 0)
    (source : ProcessionChoice l) :
    (actualTwoColumnComparison I n shift source).outputEquiv ≠
      Equiv.refl (ProcessionChoice l) :=
  finiteKernelTwoColumnComparison_outputEquiv_ne_refl l I n shift hshift source

/-- The actual reduced APT transport for the two algorithm instances, given
 the missing SHE landing for their ProcessionChoice output. -/
noncomputable def actualAPTTransport
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l) (source : ProcessionChoice l)
    (landing : SourceLocalizationExpressible
      (SHELandingActual.oneColumnStructure (k := k)) (ProcessionChoice l)) :
    SourceAlgorithmicParallelTransport
      (SHELandingActual.oneColumnStructure (k := k))
      (finiteKernelSourceAlgorithm l I n (finiteKernelComparisonInput l source))
      (finiteKernelSourceAlgorithm l I (n + 1)
        (finiteKernelComparisonInput l (ProcessionChoice.ind2Act shift source))) where
  comparison := actualTwoColumnComparison I n shift source
  landing := landing

/-- The actual APT statement follows from the actual comparison plus the
 exact missing SHE landing primitive. -/
theorem actualAPTStatement_of_landing
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))
    (n : Int) (shift : finiteLabel l) (source : ProcessionChoice l)
    (landing : SourceLocalizationExpressible
      (SHELandingActual.oneColumnStructure (k := k)) (ProcessionChoice l)) :
    SourceAPTStatement (SHELandingActual.oneColumnStructure (k := k))
      (finiteKernelSourceAlgorithm l I n (finiteKernelComparisonInput l source))
      (finiteKernelSourceAlgorithm l I (n + 1)
        (finiteKernelComparisonInput l (ProcessionChoice.ind2Act shift source))) :=
  ⟨actualAPTTransport I n shift source landing⟩

/- Exact missing primitive: SHELandingForProcessionChoice k from
SHEOutputAlignmentActual. The actual TwoActionEquivalence is constructed above;
there is no missing action-compatibility field. -/

#check actualTwoColumnComparison
#check actualTwoColumnComparison_nontrivial
#check actualAPTTransport
#check actualAPTStatement_of_landing

end LeanFormal.IUT.Theorem311Source.APTComparisonFromSource

end
