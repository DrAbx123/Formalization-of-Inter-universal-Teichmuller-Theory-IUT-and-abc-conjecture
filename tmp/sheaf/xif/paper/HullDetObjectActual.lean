/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S2723GlobalIQHullActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.Mzk1QPilotR4Stage5AlignActual

/-!
# HullDetObjectActual (A499/A501/A502/A509: O6 hull+det objects)

Object-construction pass for the hull+det triangle. A509 fallback: dependencies are
restricted to already-green oleans: Mzk1HullDetStep3115Actual (hull/det readouts),
S3137 C3 packet normalization, S3137 q-pilot reading, S2723 literal global IQ hull,
S201 root norm, the literal double-image q readout, and the old-API adic
completion/ramification files. No Takkun/O2 dependency is required here.

Objects (all with _constructed theorems to fixed real definitions):
* local/global Theta-pilot log-volume from the ACTUAL root of q:
  localQrootLogVolume = log norm(rootNormedElement),
  localThetaPilotLogVolume = log norm(rootNormedThetaValueInL j)
  = gaussExponent j * localQrootLogVolume (independent of q/(2l));
* local/global q-pilot log-volume (qPilotLogImage / qPilotLogVolumeReading);
* literal global IQ hull and its global Haar log-volume (S2723);
* det-normalized log-volume log Haar(S)/[C3 block : Q_p] with p-scaling law;
* actual C3 hull-shell/ramification data (old-API ramification index and shells).
No comparison is used in this file. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.HullDetObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotR4Stage5AlignActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

universe u

/-! ## 1. Local/global Theta-pilot log-volume from the actual 2l-root (no q/(2l)) -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Local q-root log-volume: the log norm of the actual root element
rootNormedElement (the 2l-th root of the q parameter). -/
noncomputable def localQrootLogVolume (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log (rootNormedElementNorm T b)

theorem localQrootLogVolume_constructed (b : Bad (nativePlaceSelection T)) :
    localQrootLogVolume T b = Real.log ‖rootNormedElement T b‖ := rfl

/-- Local Theta-pilot log-volume at one bad place and signed label: the log norm
of the actual root theta value in L_b (the gaussExponent power of the q-root). -/
noncomputable def localThetaPilotLogVolume (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖

theorem localThetaPilotLogVolume_constructed (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    localThetaPilotLogVolume T j b =
      Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ := rfl

/-- The independent Theta readout formula: gaussExponent j times the actual
q-root log-volume (no q/(2l) division; the root relation does the work). -/
theorem localThetaPilotLogVolume_eq_gaussExponent_mul
    (j : SignedLabel l.value) (b : Bad (nativePlaceSelection T)) :
    localThetaPilotLogVolume T j b =
      (gaussExponent j.1 : Real) * localQrootLogVolume T b := by
  unfold localThetaPilotLogVolume localQrootLogVolume
  rw [rootNormedThetaValueInL_norm, Real.log_zpow]
  rfl

/-- Global Theta-pilot log-volume: sum over the actual bad locus of the local
root-theta log-volumes. -/
noncomputable def thetaPilotLogVolume
    [Fintype (Bad (nativePlaceSelection T))] (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T), localThetaPilotLogVolume T j b

theorem thetaPilotLogVolume_constructed
    [Fintype (Bad (nativePlaceSelection T))] (j : SignedLabel l.value) :
    thetaPilotLogVolume T j =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ := rfl

theorem thetaPilotLogVolume_eq_gaussExponent_mul_sum
    [Fintype (Bad (nativePlaceSelection T))] (j : SignedLabel l.value) :
    thetaPilotLogVolume T j =
      (gaussExponent j.1 : Real) *
        ∑ b : Bad (nativePlaceSelection T), localQrootLogVolume T b := by
  unfold thetaPilotLogVolume
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact localThetaPilotLogVolume_eq_gaussExponent_mul T j b

/-- Procession average of the global Theta-pilot log-volume over the signed labels. -/
noncomputable def thetaPilotLogVolumeAverage
    [Fintype (Bad (nativePlaceSelection T))] [Fintype (SignedLabel l.value)] : Real :=
  (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
    ∑ j : SignedLabel l.value, thetaPilotLogVolume T j

theorem thetaPilotLogVolumeAverage_constructed
    [Fintype (Bad (nativePlaceSelection T))] [Fintype (SignedLabel l.value)] :
    thetaPilotLogVolumeAverage T =
      (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
        ∑ j : SignedLabel l.value, thetaPilotLogVolume T j := rfl

/-! ## 2. Local/global q-pilot readouts (independent of Theta) -/

/-- Local q-pilot readout at a native bad place: the exact local signed q-log.
negative. -/
noncomputable def localQPilotLogVolume (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotLogImage T b

theorem localQPilotLogVolume_constructed (b : Bad (nativePlaceSelection T)) :
    localQPilotLogVolume T b = Real.log ‖(qVFamily T b).q‖ := rfl

theorem localQPilotLogVolume_neg (b : Bad (nativePlaceSelection T)) :
    localQPilotLogVolume T b < 0 := qPilotLogImage_neg T b

variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i : C3.tensorIndex, Fintype (C3.tensorPlaceIndex i)]

/-- Global q-pilot readout on the actual C3 input: the signed q-pilot log-volume
-|log q| of the actual paper q-pilot object. -/
noncomputable def qPilotLogVolume
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Real :=
  qPilotLogVolumeReading P

theorem qPilotLogVolume_constructed
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolume P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

theorem qPilotLogVolume_nonpos
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolume P ≤ 0 := qPilotLogVolumeReading_nonpos P

/-! ## 3. Literal global IQ hull / Haar readout -/

local instance hullDetBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance hullDetBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The literal global IQ hull: the actual global tensor integral region. -/
noncomputable def literalIQHull (n : Nat) :
    Set (GlobalIQAmbient (C3 := C3) n) :=
  globalIQHull (C3 := C3) n

theorem literalIQHull_constructed (n : Nat) :
    literalIQHull C3 n = globalIQUnitRegion (C3 := C3) n := rfl

/-- The literal hull log-volume: the actual global Haar log-volume of the literal
global IQ hull (ENNReal). -/
noncomputable def literalIQHullLogVolume (n : Nat) : ENNReal :=
  globalIQLogVolume (C3 := C3) n (literalIQHull (C3 := C3) n)

theorem literalIQHullLogVolume_constructed (n : Nat) :
    literalIQHullLogVolume n =
      globalIQLogVolume (C3 := C3) n (globalIQUnitRegion (C3 := C3) n) := rfl

theorem literalIQHullLogVolume_lt_top (n : Nat) :
    literalIQHullLogVolume n < ⊤ :=
  globalIQUnitRegion_logVolume_lt_top (C3 := C3) n

/-! ## 4. Det normalization object (actual C3 packet normalization) -/

/-- O6-det object: the actual packet/det-normalized log-volume of a region of the
actual C3 log-shell tensor block, log Haar(S) / [block : Q_p]. -/
noncomputable def detNormalizedLogVolume
    (S : Set (C3LogShellTensorBlock C3)) : Real :=
  c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) S

theorem detNormalizedLogVolume_constructed
    (S : Set (C3LogShellTensorBlock C3)) :
    detNormalizedLogVolume C3 S =
      Real.log ((actualC3LogShellTensorHaar C3) S).toReal /
        (c3TensorBlockDimension C3 : Real) := rfl

/-- The det normalization applied to the actual theta-pilot hull computes the
actual region log-volume divided by the actual Q_p-dimension (uses the proved
hull=region equality). -/
theorem detNormalizedLogVolume_hullRegion_constructed :
    detNormalizedLogVolume C3 (thetaPilotHull C3) =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal /
        (c3TensorBlockDimension C3 : Real) := by
  rw [thetaPilotHull_eq_region]
  rfl

/-- The det normalization has the actual p-scaling law +(-log p) (IUT III,
Proposition 3.9 (i), at the actual C3 carrier). -/
theorem detNormalizedLogVolume_prime_smul
    {S : Set (C3LogShellTensorBlock C3)}
    (hpos : 0 < (actualC3LogShellTensorHaar C3) S)
    (hfin : (actualC3LogShellTensorHaar C3) S < ⊤) :
    detNormalizedLogVolume C3 ((C3.p : ℚ_[C3.p]) • S) =
      -Real.log (C3.p : Real) + detNormalizedLogVolume C3 S :=
  c3PacketNormalizedLogVolume_prime_smul (C3 := C3)
    (actualC3LogShellTensorHaar C3) hpos hfin

/-! ## 5. Actual C3 hull shell / ramification data (old-API, no Takkun) -/

section C3HullShell

/-- The actual ramification index of the C3 finite place over Q_p. -/
noncomputable def c3RamificationIndex : Nat :=
  (comap (k := ℚ) C3.place.val).maximalIdeal.asIdeal.ramificationIdx'
    C3.place.val.maximalIdeal.asIdeal

theorem c3RamificationIndex_pos : 0 < c3RamificationIndex C3 :=
  Nat.pos_of_ne_zero (ramificationIdx_ne_zero (k := ℚ) C3.place.val)

/-- The actual C3 log-shell of exponent lam in the actual completion of Fmod. -/
noncomputable def c3HullShell (lam : Int) :
    Set (CommonPrimeCompletion C3.place) :=
  {x | ‖x‖ <= (C3.p : Real) ^ (-lam)}

/-- The exponent-zero C3 log-shell is the actual integral region. -/
theorem c3HullShell_zero :
    c3HullShell C3 0 = (Integers (CommonPrimeCompletion C3.place) :
      Set (CommonPrimeCompletion C3.place)) := by
  ext x
  simp [c3HullShell, mem_integers_iff]

theorem c3IntegralRegion_subset_shell_zero :
    (Integers (CommonPrimeCompletion C3.place) :
        Set (CommonPrimeCompletion C3.place)) <= c3HullShell C3 0 := by
  rw [c3HullShell_zero]

/-- Shell inclusion monotonically reflects the exponent order: larger exponent
lam means smaller shell. -/
theorem c3HullShell_antitone {lam mu : Int} (h : mu <= lam) :
    c3HullShell C3 lam <= c3HullShell C3 mu := by
  intro x hx
  have hp1 : (1 : Real) < (C3.p : Real) := by
    exact_mod_cast C3.hp.out.one_lt
  have hz : -(lam : Int) <= -(mu : Int) := by omega
  have hpow : (C3.p : Real) ^ (-(lam : Int)) <=
      (C3.p : Real) ^ (-(mu : Int)) :=
    zpow_le_zpow_right₀ hp1.le hz
  exact le_trans hx hpow

/-- The actual C3 hull shell data object (p, ramification index, shells). -/
structure C3HullShellData
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  p : Nat
  e : Nat
  p_eq : p = C3.p
  e_eq : e = c3RamificationIndex C3
  shell : Int -> Set (CommonPrimeCompletion C3.place)
  shell_eq : shell = c3HullShell C3
  shell_zero_eq : shell 0 = (Integers (CommonPrimeCompletion C3.place) :
    Set (CommonPrimeCompletion C3.place))
  shell_antitone : forall {lam mu : Int}, mu <= lam -> shell lam <= shell mu

noncomputable def c3HullShellData : C3HullShellData C3 where
  p := C3.p
  e := c3RamificationIndex C3
  p_eq := rfl
  e_eq := rfl
  shell := c3HullShell C3
  shell_eq := rfl
  shell_zero_eq := c3HullShell_zero C3
  shell_antitone := c3HullShell_antitone C3

theorem c3HullShellData_constructed :
    (c3HullShellData C3).p = C3.p ∧
    (c3HullShellData C3).e = c3RamificationIndex C3 ∧
    (c3HullShellData C3).shell = c3HullShell C3 := by
  refine ⟨rfl, rfl, rfl⟩

end C3HullShell

/-! ## 6. O6 package and the HDD readout bridge -/

/-- Bridge to the green hull/det readouts: the packet log-volume is the HDD hull
readout at a concrete HullDetState. -/
theorem hdd_hullReadout_eq_packetLogVolume {label : Type u} [Fintype label]
    (x : Mzk1HullDetStep3115Actual.HullDetState label) :
    Mzk1HullDetStep3115Actual.hullReadout x = packetLogVolume x.packet := rfl

/-- O6 hull/det object package on one actual C3 input, one signed label and one
global IQ hull level. -/
structure HullDetObjects (T : SourceNativeInitialThetaData.{0} l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    [Fintype (Bad (nativePlaceSelection T))]
    (P : PaperQPilotObjectActual (l := l) (I := I))
    (j : SignedLabel l.value) (n : Nat) where
  thetaLogVolume : Real
  thetaLogVolume_constructed : thetaLogVolume = thetaPilotLogVolume T j
  qLogVolume : Real
  qLogVolume_constructed : qLogVolume = qPilotLogVolume P
  literalHullLogVolume : ENNReal
  literalHullLogVolume_constructed : literalHullLogVolume =
    globalIQLogVolume (C3 := C3) n (literalIQHull (C3 := C3) n)
  detNormalizedVolume : Real
  detNormalizedVolume_constructed : detNormalizedVolume =
    detNormalizedLogVolume C3 (actualC3LogShellTensorRegion C3)

noncomputable def hullDetObjects
    (T : SourceNativeInitialThetaData.{0} l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    [Fintype (Bad (nativePlaceSelection T))]
    (P : PaperQPilotObjectActual (l := l) (I := I))
    (j : SignedLabel l.value) (n : Nat) : HullDetObjects T C3 P j n where
  thetaLogVolume := thetaPilotLogVolume T j
  thetaLogVolume_constructed := rfl
  qLogVolume := qPilotLogVolume P
  qLogVolume_constructed := rfl
  literalHullLogVolume := globalIQLogVolume (C3 := C3) n (literalIQHull (C3 := C3) n)
  literalHullLogVolume_constructed := rfl
  detNormalizedVolume := detNormalizedLogVolume C3 (actualC3LogShellTensorRegion C3)
  detNormalizedVolume_constructed := rfl

end LeanFormal.IUT.XiFPaper.HullDetObjectActual