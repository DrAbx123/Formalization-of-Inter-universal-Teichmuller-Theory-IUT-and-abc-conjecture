import tmp.sheaf.xif.paper.NativeSourceAssemblyFieldsActual
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.PaperXiFUnconditional
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# Assembly fields, Kummer/Ind actions and Theta-link/PaperUnconditionalData

This is the actual consumer bridge between the reusable source assembly fields,
the actual global Kummer/Ind actions, and the paper Theta-link/unconditional data
surface.

The assembly carrier fields and the global Kummer/Ind data are actual inhabitants.
The ThetaLinkActual and PaperUnconditionalData are consumed as their explicit
paper structures; no identification or compatibility equality is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.AssemblyKummerIndThetaPaperBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFieldsActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.XiFPaper.ThetaLink

universe u ua uv upi umon ui uG uX uLabel uL uC

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable {A : CapsuleTheaterAssignment l V I}
variable {C : SourceProcessionCapsuleContract Real l V I}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (P : PaperSignedHull X label)
variable (v : V)

/-- Actual assembly carrier fields, actual global Kummer/Ind data, and the
paper Theta-link/unconditional data surface. -/
structure AssemblyKummerIndThetaPaperData
    (T : SourceNativeInitialThetaData.{0} l) where
  carrierFields : ActualNativeAssemblyCarrierFields.{0}
  kummerInd : GlobalKummerIndActionsData (I := I) A C C3
  thetaLink : ThetaLinkActual O P C3
  paperData : PaperUnconditionalData (label := label) v O P C3

/-- Construct the bridge from the actual carriers/actions and supplied paper
structures. -/
noncomputable def assemblyKummerIndThetaPaperData
    (L : ThetaLinkActual O P C3)
    (D : PaperUnconditionalData (label := label) v O P C3) :
    AssemblyKummerIndThetaPaperData (l := l) (V := V) (I := I)
      (A := A) (C := C) (C3 := C3) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (O := O) (P := P) (v := v) (T := T) where
  carrierFields := actualNativeAssemblyCarrierFields T
  kummerInd := globalKummerIndActionsData (I := I) (A := A) (C := C) C3
  thetaLink := L
  paperData := D

/-- Recyclable projection: the actual assembly carrier fields. -/
theorem assemblyKummerIndThetaPaperData_carrierFields
    (L : ThetaLinkActual O P C3)
    (D : PaperUnconditionalData (label := label) v O P C3) :
    (assemblyKummerIndThetaPaperData (l := l) (V := V) (I := I)
      (A := A) (C := C) (C3 := C3) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (O := O) (P := P) (v := v) (T := T) L D).carrierFields =
      actualNativeAssemblyCarrierFields (l := l) (T := T) := rfl

/-- Projection: the actual global Kummer/Ind arrows and actions. -/
theorem assemblyKummerIndThetaPaperData_kummerInd
    (L : ThetaLinkActual O P C3)
    (D : PaperUnconditionalData (label := label) v O P C3) :
    (assemblyKummerIndThetaPaperData (l := l) (V := V) (I := I)
      (A := A) (C := C) (C3 := C3) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (O := O) (P := P) (v := v) (T := T) L D).kummerInd =
      globalKummerIndActionsData (I := I) (A := A) (C := C) C3 := rfl

/-- Projection: the paper Theta-link. -/
theorem assemblyKummerIndThetaPaperData_thetaLink
    (L : ThetaLinkActual O P C3)
    (D : PaperUnconditionalData (label := label) v O P C3) :
    (assemblyKummerIndThetaPaperData (l := l) (V := V) (I := I)
      (A := A) (C := C) (C3 := C3) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (O := O) (P := P) (v := v) (T := T) L D).thetaLink = L := rfl

/-- Projection: the paper unconditional data. -/
theorem assemblyKummerIndThetaPaperData_paperData
    (L : ThetaLinkActual O P C3)
    (D : PaperUnconditionalData (label := label) v O P C3) :
    (assemblyKummerIndThetaPaperData (l := l) (V := V) (I := I)
      (A := A) (C := C) (C3 := C3) (G := G) (envStrip := envStrip)
      (X := X) (label := label) (O := O) (P := P) (v := v) (T := T) L D).paperData = D := rfl

end LeanFormal.IUT.XiFPaper.AssemblyKummerIndThetaPaperBridgeActual

end