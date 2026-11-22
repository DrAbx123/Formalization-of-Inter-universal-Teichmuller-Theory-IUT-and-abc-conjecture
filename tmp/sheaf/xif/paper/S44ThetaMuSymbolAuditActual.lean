import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Mathlib.RingTheory.RootsOfUnity.Basic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! # S44: Theta/theta and mu-carrier audit objects

This file constructs the actual carrier data used by the S44 audit:

* ThetaPilotCarrier versus FiniteThetaPacket (Theta versus theta);
* the actual mu_{2l} roots in F_mod (the finite-place roots group) and in a
  completion, as distinct carriers.

No equality between Theta and theta carriers and no equality between
mu(F_mod^x) and local mu_{2l} is asserted.  The file only packages the actual
carrier types/subgroups and their type equalities.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S44ThetaMuSymbolAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]

/-- Actual Theta-pilot carrier type, kept separate from theta packet. -/
abbrev ThetaPilotObjectCarrier : Type := ThetaPilotCarrier l

/-- Actual lowercase theta packet carrier type. -/
abbrev ThetaPacketValueCarrier : Type := FiniteThetaPacket l

/-- Audit package: Theta-pilot object and theta packet are different carriers. -/
structure ThetaThetaCarrierAudit where
  thetaPilot : Type
  thetaPilot_eq : thetaPilot = ThetaPilotObjectCarrier (l := l)
  thetaPacket : Type
  thetaPacket_eq : thetaPacket = ThetaPacketValueCarrier (l := l)

/-- Actual Theta/theta carrier audit data. -/
def thetaThetaCarrierAudit : ThetaThetaCarrierAudit (l := l) where
  thetaPilot := ThetaPilotObjectCarrier (l := l)
  thetaPilot_eq := rfl
  thetaPacket := ThetaPacketValueCarrier (l := l)
  thetaPacket_eq := rfl

/-- Actual paper mu(F_mod^x) root subgroup of order 2l. -/
noncomputable def paperMuFmodRoots
    {l : PrimeGeFive} (A : InitialThetaArithmeticData l) :=
  rootsOfUnity (2 * l.value) A.Fmod

/-- Actual local completion mu_{2l} root subgroup. -/
noncomputable def paperMuCompletionRoots
    {l : PrimeGeFive} {K : Type u} [Field K] [NumberField K]
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime K p) :=
  rootsOfUnity (2 * l.value) (CommonPrimeCompletion place)

/-- Audit package: F_mod roots and completion roots are different carriers. -/
structure MuCarrierAudit
    (A : InitialThetaArithmeticData l) (place : FinitePlaceAtPrime K p) where
  fmodRoots : Subgroup A.Fmodˣ
  fmodRoots_eq : fmodRoots = paperMuFmodRoots (l := l) A
  localRoots : Subgroup (CommonPrimeCompletion place)ˣ
  localRoots_eq : localRoots = paperMuCompletionRoots (l := l) place

/-- Actual mu carrier audit data. -/
noncomputable def muCarrierAudit
    (A : InitialThetaArithmeticData l) (place : FinitePlaceAtPrime K p) :
    MuCarrierAudit (l := l) A place where
  fmodRoots := paperMuFmodRoots (l := l) A
  fmodRoots_eq := rfl
  localRoots := paperMuCompletionRoots (l := l) place
  localRoots_eq := rfl

end LeanFormal.IUT.XiFPaper.S44ThetaMuSymbolAuditActual

end
