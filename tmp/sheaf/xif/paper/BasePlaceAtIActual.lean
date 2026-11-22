import tmp.sheaf.xif.paper.C3DonorUnconditionalActual
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.n8.closure.C10BridgeProof
import tmp.sheaf.n8.closure.NativeC3

/-!
# Actual BasePlaceAtI construction

Task-628 constructs the BasePlaceAtI package used by
C3DonorUnconditionalActual:

  fmod_eq : X.S.arithmetic.Fmod = I.initial.arithmetic.Fmod
  hp      : Fact (nativeC3Prime X).Prime
  place   : FinitePlaceAtPrime I.initial.arithmetic.Fmod (nativeC3Prime X).

The prime/place side is actual native data:
* nativeC3Prime X is the rational prime of nativeBadBasePlace X;
* nativeC3Prime_prime X proves it is prime;
* nativeC3Place X is the actual base place as a FinitePlaceAtPrime.

The only missing coherence is the Fmod equality between the native root's
Fmod and the selected OriginalInput's Fmod.  C10BridgeProof supplies the exact
bridge: a NativeOriginalInputDonors X contains

  initial_arithmetic : D.initial.arithmetic = X.S.arithmetic,

and nativeOriginalInputOfDonors X D has that initial arithmetic.  Therefore the
actual BasePlaceAtI is constructed from X plus that donor, with the place
transported along the resulting Fmod equality.  No arbitrary place is chosen.

The unconditional native-to-contract coherence is still a source gap: there is
no production declaration constructing SourceDefinition31Data from X.S alone
(C10BridgeProof's donor is the exact missing input).  This file reports that
missing donor/coherence and writes the conditional actual constructor.

No arbitrary place/True/PUnit/axiom/sorry.  WRITE-ONLY; compilation queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BasePlaceAtIActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {V : Type uv} (I : OriginalInput l V)

/-! ## 1. Actual BasePlaceAtI from an explicit Fmod coherence -/

/-- Construct BasePlaceAtI from the native prime/place and an explicit
coherence between the native root Fmod and the selected OriginalInput Fmod.
The place is the actual nativeC3Place transported along h; no place is chosen
arbitrarily. -/
noncomputable def basePlaceAtIOfFmodEq
    (h : X.S.arithmetic.Fmod = I.initial.arithmetic.Fmod) :
    BasePlaceAtI (I := I) where
  fmod_eq := h
  hp := ⟨nativeC3Prime_prime X⟩
  place := h ▸ nativeC3Place X

/-- The constructed place is the actual nativeC3Place, transported along the
supplied Fmod equality. -/
theorem basePlaceAtIOfFmodEq_place
    (h : X.S.arithmetic.Fmod = I.initial.arithmetic.Fmod) :
    (basePlaceAtIOfFmodEq (X := X) (I := I) h).place =
      h ▸ nativeC3Place X := rfl

/-- The constructed package's h field is the supplied coherence. -/
theorem basePlaceAtIOfFmodEq_fmod_eq
    (h : X.S.arithmetic.Fmod = I.initial.arithmetic.Fmod) :
    (basePlaceAtIOfFmodEq (X := X) (I := I) h).fmod_eq = h := rfl

/-! ## 2. Actual BasePlaceAtI from the C10 native donor -/

/-- The actual Fmod coherence produced by a C10 NativeOriginalInputDonors:
the donor's initial arithmetic equals the native arithmetic. -/
def fmodEqOfNativeDonors (D : NativeOriginalInputDonors (X := X)) :
    X.S.arithmetic.Fmod =
      (nativeOriginalInputOfDonors (X := X) D).initial.arithmetic.Fmod := by
  change X.S.arithmetic.Fmod = D.initial.arithmetic.Fmod
  exact congrArg (fun A : InitialThetaArithmeticData l => A.Fmod)
    D.initial_arithmetic.symm

/-- The actual BasePlaceAtI for the C10 donor-built OriginalInput. -/
noncomputable def basePlaceAtIOfNativeDonors
    (D : NativeOriginalInputDonors (X := X)) :
    BasePlaceAtI (I := nativeOriginalInputOfDonors (X := X) D) :=
  basePlaceAtIOfFmodEq (X := X)
    (I := nativeOriginalInputOfDonors (X := X) D)
    (fmodEqOfNativeDonors (X := X) D)

/-- The donor-built package has the actual nativeC3Place transported along the
native-donor Fmod coherence. -/
theorem basePlaceAtIOfNativeDonors_place
    (D : NativeOriginalInputDonors (X := X)) :
    (basePlaceAtIOfNativeDonors (X := X) D).place =
      fmodEqOfNativeDonors (X := X) D ▸ nativeC3Place X := rfl

/-- The donor-built package's coherence is the actual C10 coherence. -/
theorem basePlaceAtIOfNativeDonors_fmod_eq
    (D : NativeOriginalInputDonors (X := X)) :
    (basePlaceAtIOfNativeDonors (X := X) D).fmod_eq =
      fmodEqOfNativeDonors (X := X) D := rfl

/-! ## 3. Exact missing unconditional coherence -/

/-- Exact missing source coherence for the unconditional BasePlaceAtI: an
actual construction of the C10 NativeOriginalInputDonors from X.S alone, in
particular the Fmod equality with the selected OriginalInput. -/
def MissingUnconditionalNativeFmodCoherence : Prop :=
  Nonempty (NativeOriginalInputDonors (X := X))

/-- The missing donor is exactly what supplies the conditional BasePlaceAtI
constructor. -/
theorem basePlaceAtIOfNativeDonors_exists_of_donor
    (D : NativeOriginalInputDonors (X := X)) :
    Nonempty (BasePlaceAtI (I := nativeOriginalInputOfDonors (X := X) D)) :=
  ⟨basePlaceAtIOfNativeDonors (X := X) D⟩

/-- The unconditional BasePlaceAtI is not asserted from X.S alone; the exact
missing input is the C10 native donor/coherence. -/
theorem missingUnconditionalNativeFmodCoherence_iff :
    MissingUnconditionalNativeFmodCoherence (X := X) ↔
      Nonempty (NativeOriginalInputDonors (X := X)) := Iff.rfl

end LeanFormal.IUT.XiFPaper.BasePlaceAtIActual
