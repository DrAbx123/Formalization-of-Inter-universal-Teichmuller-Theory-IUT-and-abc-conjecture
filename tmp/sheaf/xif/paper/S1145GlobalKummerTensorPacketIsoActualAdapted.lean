import tmp.sheaf.xif.paper.Theorem311KummerPacketIsoGapActual
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1145GlobalKummerTensorPacketIsoActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.Theorem311KummerPacketIsoGapActual
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open MeasureTheory

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Actual local tensor-packet isomorphisms from the global Kummer/Ind data. -/
def s1145LocalPacketIso (K : GlobalKummerIndActionsData I A C C3) : Prop :=
  Nonempty (∀ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j),
    ActualTensorPacket C j vQ ≃ₗ[Real]
      (⨂[Real] (i : Capsule j.val),
        DirectSumFactor (C.logShell j) vQ (P.perm.symm i)))

/-- Actual Ind2/product isomorphisms from the global Kummer/Ind data. -/
def s1145ProductCompatibility (K : GlobalKummerIndActionsData I A C C3) : Prop :=
  Nonempty (∀ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ),
    SourceProcessionCapsuleContract.tensorPacket Real C j vQ ≃ₗ[Real]
      SourceProcessionCapsuleContract.tensorPacket Real C j vQ)

/-- Actual global Theta packet datum. -/
def s1145GlobalThetaPacket (K : GlobalKummerIndActionsData I A C C3) : Prop :=
  Nonempty (FiniteThetaPacket l)

/-- Construct the exact GlobalKummerTensorPacketIso fields from the actual
local isomorphisms, product isomorphisms and global Theta packet. -/
noncomputable def globalKummerTensorPacketIsoOfActions
    (K : GlobalKummerIndActionsData I A C C3) :
    GlobalKummerTensorPacketIso where
  localPacketIso := s1145LocalPacketIso I A C C3 K
  globalTensorIso := s1145GlobalThetaPacket I A C C3 K
  productCompatibility := s1145ProductCompatibility I A C C3 K
  globalThetaPacketCompatibility := s1145GlobalThetaPacket I A C C3 K

/-- The gap predicate is inhabited from the actual fields; no True is used. -/
theorem globalKummerTensorPacketIsoRequired_actual
    (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract Real l V I)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    GlobalKummerTensorPacketIsoRequired :=
  ⟨globalKummerTensorPacketIsoOfActions I A C C3
    (globalKummerIndActionsData I A C C3)⟩

/-- Exact minimum: the actual GlobalKummerIndActionsData plus the local/product/
globalTheta fields above. -/
def S1145ExactMinimum : Prop :=
  GlobalKummerTensorPacketIsoRequired

end LeanFormal.IUT.XiFPaper.S1145GlobalKummerTensorPacketIsoActualAdapted

end
