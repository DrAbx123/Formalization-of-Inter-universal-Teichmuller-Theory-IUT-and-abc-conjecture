import tmp.sheaf.xif.paper.SHEOperationsFromSource
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialColumnInsensitivity
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT

/-! # CONDITIONAL STATUS (xi-f)

Conditional: production finiteKernelSourceAlgorithm is used, but output alignment ProcessionChoice ~ SHE Output and SHE landing over ProcessionChoice are missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual multiradial algorithm from source finite-kernel data

Builds the actual `SourceTheorem311MultiradialAlgorithm` supplied by the
source finite-kernel wiring: the finite Q(i)-at-5 carrier, the finite-kernel
(Ind1) procession action, and the finite-kernel (Ind2) translation action.
The algorithm output carrier is the actual `ProcessionChoice l`, not an
arbitrary abstract carrier. The construction is the production
`finiteKernelSourceAlgorithm`, not the trivial-action gate.

The remaining bridge to the SHE operation-level output is exact:
* the actual algorithm output is `ProcessionChoice l`, while the SHE
  operation landing has output carrier the integral sections `Output k`;
* a carrier equivalence `ProcessionChoice l ≃ Output k` is not supplied;
* a SHE landing `SourceLocalizationExpressible S (ProcessionChoice l)` is
  not supplied by the integral-section landing.
These are reported as exact primitives; no toy algorithm/True/PUnit/sorry/
axiom is introduced. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring

universe ua uv upi umon ui

variable {V : Type uv} {l : PrimeGeFive}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n : Int}

/-- The actual algorithm output carrier supplied by the finite-kernel source
construction. -/
abbrev ActualAlgorithmOutput : Type := ProcessionChoice l

/-- The actual source multiradial algorithm instance: finite-kernel carrier,
actual (Ind1) procession action, actual (Ind2) kernel translation action. -/
noncomputable def actualSourceAlgorithm
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l)) :
    SourceTheorem311MultiradialAlgorithm
      (Multiplicative (finiteLabel l)) (Multiplicative (finiteLabel l))
      I n (ActualAlgorithmOutput (l := l)) :=
  finiteKernelSourceAlgorithm l I n input

/-- The actual algorithm's (Ind1) action is the finite-kernel procession
translate (production computation law). -/
@[simp] theorem actualSourceAlgorithm_ind1Action_apply
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l))
    (g : Multiplicative (finiteLabel l)) (c : ActualAlgorithmOutput (l := l)) :
    (actualSourceAlgorithm (I := I) (n := n) input).ind1Action g c =
      ProcessionChoice.ind1Act (Multiplicative.toAdd g) c := by
  exact finiteKernelSourceAlgorithm_ind1Action_apply l I n input g c

/-- The actual algorithm's (Ind2) action is the finite-kernel translation
(production computation law). -/
@[simp] theorem actualSourceAlgorithm_ind2Action_apply
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l))
    (g : Multiplicative (finiteLabel l)) (c : ActualAlgorithmOutput (l := l)) :
    (actualSourceAlgorithm (I := I) (n := n) input).ind2Action g c =
      ProcessionChoice.ind2Act (Multiplicative.toAdd g) c := by
  exact finiteKernelSourceAlgorithm_ind2Action_apply l I n input g c

/-- The actual algorithm is non-trivial: the (Ind2) action moves the base
choice at a nonzero generator shift. This rules out the trivial gate. -/
theorem actualSourceAlgorithm_nontrivial :
    ∃ g : Multiplicative (finiteLabel l), g ≠ 1 ∧
      (actualSourceAlgorithm (I := I) (n := n)
        (input := finiteKernelComparisonInput l ProcessionChoice.base)
      ).ind2Action g ProcessionChoice.base ≠ ProcessionChoice.base := by
  rcases finiteKernelInd2ActionData_nontrivial l with ⟨g, hg, hgbase⟩
  refine ⟨g, hg, ?_⟩
  simpa using hgbase

/-- The exact primitive output-carrier equivalence between the actual
algorithm output ProcessionChoice l and the SHE integral-section output
carrier Output k. This is not supplied by the current source. -/
def OutputCarrierAlignment (k : Type) [Field k] [NumberField k] : Prop :=
  Nonempty (ActualAlgorithmOutput (l := l) ≃ SHELandingActual.Output (k := k))

/-- The exact primitive SHE landing for the actual algorithm output carrier. -/
def SHELandingForAlgorithmOutput
    (k : Type) [Field k] [NumberField k] : Prop :=
  SourceLocalizationExpressible (SHELandingActual.oneColumnStructure (k := k))
    (ActualAlgorithmOutput (l := l))

/- Exact missing fields for discharge of the SHE/APT algorithm primitive:
1. OutputCarrierAlignment k: an actual equivalence between ProcessionChoice l
   and the SHE integral-section output carrier;
2. SHELandingForAlgorithmOutput k: a SHE landing for the actual
   ProcessionChoice output, not the integral-section Output carrier.
The actual SourceTheorem311MultiradialAlgorithm itself is constructed above;
no arbitrary/toy instance is used. -/

#check actualSourceAlgorithm
#check actualSourceAlgorithm_ind1Action_apply
#check actualSourceAlgorithm_ind2Action_apply
#check actualSourceAlgorithm_nontrivial
#check OutputCarrierAlignment
#check SHELandingForAlgorithmOutput

end LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource

end
