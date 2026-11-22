import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.SHEAlgorithmFromSource

/-! # CONDITIONAL STATUS (xi-f)

Constructs an index reading, but explicitly NOT a source-faithful ProcessionChoice/SHE Output alignment. No paper SHE alignment is asserted.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Constructive index reading for ProcessionChoice

This file constructs an actual `SourceLocalizationExpressible` reading for
the actual algorithm output `ProcessionChoice l`, using a concrete integer
index built from all three actual coordinates (two `ZMod l` labels and the
Ind3 level). The resulting bundle has total `ProcessionChoice l`, and its
localization is the actual completed-ring localization of the integer index.

IMPORTANT: this is a concrete index reading, not a source-faithful
identification of the multiradial output with the integral-section carrier.
It is not claimed to be the paper SHE output alignment. The exact missing
object is a source-faithful equivalence/reading, not merely any bijection or
index encoding. No toy/constant/zero reading, no axiom/sorry. WRITE-ONLY: no
lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.ProcessionAlignmentConstructionAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.ConcreteFiniteTheorem311

variable {k : Type} [Field k] [NumberField k] {l : PrimeGeFive}

/-- Concrete integer index built from the two ZMod labels and the Ind3 level. -/
def processionIndex (x : ProcessionChoice l) : Nat :=
  x.processionLabel.val *
      (l.value * (x.upperSemiLevel + 1)) +
    x.tensorLabel.val * (x.upperSemiLevel + 1) +
      x.upperSemiLevel

/-- The integer index as an integral section. -/
def processionInteger (x : ProcessionChoice l) :
    NumberField.RingOfIntegers k :=
  (processionIndex (l := l) x : NumberField.RingOfIntegers k)

/-- The actual index-reading line bundle over the completed one-column rings. -/
abbrev processionBundle :
    SourceArithmeticVectorBundle
      (SHELandingActual.oneColumnStructure (k := k)) where
  total := ProcessionChoice l
  localization v x := completionLocalization (k := k) v (processionInteger (k := k) x)

/-- Actual reading map for the ProcessionChoice output. -/
def processionReading (v : NumberField.FinitePlace k)
    (x : ProcessionChoice l) :
    (SHELandingActual.oneColumnStructure (k := k)).localRing v :=
  (processionBundle (k := k) (l := l)).localization v x

theorem processionReading_factorization
    (v : NumberField.FinitePlace k) (x : ProcessionChoice l) :
    ∃ s : (processionBundle (k := k) (l := l)).total,
      processionReading (k := k) v x =
        (processionBundle (k := k) (l := l)).localization v s :=
  ⟨x, rfl⟩

/-- Actual localization expression for the ProcessionChoice output. This is a
/-- concrete index reading, not the source-faithful SHE identification. -/
def processionExpression :
    SourceLocalizationExpression
      (SHELandingActual.oneColumnStructure (k := k)) (ProcessionChoice l) where
  bundle := processionBundle (k := k) (l := l)
  output := ProcessionChoice.base
  expression v x := processionReading (k := k) v x
  isLocalizationReading v x := processionReading_factorization (k := k) v x

/-- The concrete index reading is an actual landing. -/
theorem processionChoiceLanding_actual :
    SourceLocalizationExpressible
      (SHELandingActual.oneColumnStructure (k := k)) (ProcessionChoice l) :=
  ⟨processionExpression (k := k) (l := l)⟩

/- Exact missing object: a source-faithful equivalence/reading between
ProcessionChoice l and the SHE integral-section output carrier (or the actual
multiradial output-to-section map). The construction above is an index
reading only; it is not asserted to be the paper SHE alignment. -/

#check processionIndex
#check processionBundle
#check processionReading
#check processionChoiceLanding_actual

end LeanFormal.IUT.Theorem311Source.ProcessionAlignmentConstructionAdapted

end
