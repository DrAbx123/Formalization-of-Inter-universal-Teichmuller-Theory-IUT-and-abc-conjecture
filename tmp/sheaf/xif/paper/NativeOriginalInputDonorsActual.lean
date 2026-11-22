import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.xif.paper.BasePlaceAtIActual
import tmp.sheaf.n8.closure.NativeIndexActualAttempt

/-!
# Actual NativeOriginalInputDonors construction

Task-635 attempts to construct

  NativeOriginalInputDonors X

from the native root X.S or exact source data.

Actual available construction.  NativeSourceAssembly (T := X.S) supplies an
actual assembled SourceDefinition31Data with arithmetic equal to X.S.arithmetic.
Its assemblyDonors constructor needs exactly two external data:

1. S : NativeSourceAssembly X.S (the exact source clause fields: badFinite,
   split multiplicative reduction, torsion gaps, exact sequence, curve/cover
   data, d7 intake, cusp hypotheses, and the five compatibility proofs);
2. e : X.family.index ≃ SourceTheorem311Index.

Given those two explicit source data, assemblyDonors X S e is an actual
NativeOriginalInputDonors X with initial := S.toSourceData and
initial_arithmetic := rfl.  Therefore the BasePlaceAtI package is also actual
for the donor-built OriginalInput, via BasePlaceAtIActual.

What is missing for unconditional construction:

* no production declaration constructs NativeSourceAssembly X.S from X.S alone;
  it is the exact C3/clause source donor package;
* NativeLattice/N8NativeInput carries no index_equiv; see
  NativeIndexActualAttempt / C10BridgeProof.

No arbitrary SourceDefinition31Data, donor, equivalence, axiom or sorry is used.
This file writes the conditional actual object and records the exact missing
source fields.  WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeOriginalInputDonorsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.C1Actual
open LeanFormal.IUT.N8Closure.NativeIndexActualAttempt
open LeanFormal.IUT.XiFPaper.BasePlaceAtIActual
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-! ## 1. Actual donors from the assembled native contract -/

/-- The actual NativeOriginalInputDonors constructed from the assembled native
SourceDefinition31Data and the explicit family index equivalence. -/
noncomputable def nativeOriginalInputDonorsOfAssembly
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    NativeOriginalInputDonors (X := X) :=
  assemblyDonors (X := X) S e

/-- The constructed donor has the assembled source datum as its initial
contract object. -/
theorem nativeOriginalInputDonorsOfAssembly_initial
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    (nativeOriginalInputDonorsOfAssembly (X := X) S e).initial = S.toSourceData := rfl

/-- The constructed donor's arithmetic equality is the actual assembled
arithmetic equality. -/
theorem nativeOriginalInputDonorsOfAssembly_initial_arithmetic
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    (nativeOriginalInputDonorsOfAssembly (X := X) S e).initial_arithmetic =
      (show S.toSourceData.arithmetic = X.S.arithmetic from rfl) := rfl

/-- The constructed donor's index equivalence is the supplied actual
equivalence. -/
theorem nativeOriginalInputDonorsOfAssembly_index
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    (nativeOriginalInputDonorsOfAssembly (X := X) S e).index_equiv = e := rfl

/-! ## 2. BasePlaceAtI through the actual donor -/

/-- The actual BasePlaceAtI package for the donor-built OriginalInput. -/
noncomputable def basePlaceAtIOfAssembly
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    BasePlaceAtI (X := X)
      (nativeOriginalInputOfDonors (X := X)
        (nativeOriginalInputDonorsOfAssembly (X := X) S e)) :=
  basePlaceAtIOfNativeDonors (X := X)
    (nativeOriginalInputDonorsOfAssembly (X := X) S e)

/-- The constructed BasePlaceAtI has the actual native place. -/
theorem basePlaceAtIOfAssembly_place
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    (basePlaceAtIOfAssembly (X := X) S e).place =
      fmodEqOfNativeDonors (X := X)
        (nativeOriginalInputDonorsOfAssembly (X := X) S e) ▸ nativeC3Place X :=
  basePlaceAtIOfNativeDonors_place (X := X)
    (nativeOriginalInputDonorsOfAssembly (X := X) S e)

/-! ## 3. Exact missing source fields -/

/-- The exact source assembly donor required for the unconditional native
contract.  This is not constructed from X.S alone in the tree. -/
def MissingNativeSourceAssembly : Prop :=
  Nonempty (NativeSourceAssembly X.S)

/-- The exact missing family index equivalence. -/
def MissingNativeIndexEquiv : Prop :=
  Nonempty (X.family.index ≃ SourceTheorem311Index)

/-- The exact missing donor pair for unconditional NativeOriginalInputDonors. -/
def MissingNativeOriginalInputDonorPair : Prop :=
  MissingNativeSourceAssembly (X := X) ∧ MissingNativeIndexEquiv (X := X)

/-- The actual conditional construction exists exactly from the explicit
source assembly and index equivalence. -/
theorem nativeOriginalInputDonorsOfAssembly_exists
    (S : NativeSourceAssembly X.S)
    (e : X.family.index ≃ SourceTheorem311Index) :
    Nonempty (NativeOriginalInputDonors (X := X)) :=
  ⟨nativeOriginalInputDonorsOfAssembly (X := X) S e⟩

/-- The missing pair is exactly the pair of inputs consumed by the actual
constructor; no other source field is hidden. -/
theorem missingNativeOriginalInputDonorPair_iff :
    MissingNativeOriginalInputDonorPair (X := X) ↔
      Nonempty (NativeSourceAssembly X.S) ∧
        Nonempty (X.family.index ≃ SourceTheorem311Index) := Iff.rfl

end LeanFormal.IUT.XiFPaper.NativeOriginalInputDonorsActual
