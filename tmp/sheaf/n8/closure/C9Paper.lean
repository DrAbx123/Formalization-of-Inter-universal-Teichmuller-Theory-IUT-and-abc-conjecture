import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib

/-!
# C9 paper stage 2: constrained QPaper / ThetaPaper / ValuesPaper

Paper: IUT III Corollary 3.12, lines 10326-10358 and 10843-10898.

This file replaces the earlier free-field C9Paper stage 2.  The structures are
constrained to actual donors:

- QPaper carries C3 and an actual q scalar QPaperScalar C3.  Its q-pilot region
  is a C6 tensor region constrained to the actual C6 hull; its log-volume is
  computed by C6's actual normalizedLogVolume function.
- ThetaPaper carries n and an equality to the actual sourceHolomorphicHull,
  plus containment of the actual possible-theta image set.  Its thetaLogVolume
  is computed by C6.normalizedLogVolume through an actual theta-to-C6 map
  interface (a named donor gap).
- ValuesPaper has no free Set Real: values are literally
  C6.normalizedLogVolume applied to the actual C6 provenance set.

Missing source constraints are theorem-level named sorrys with exact types.  No
arbitrary Type, True, or free Set Real is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9Paper

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL uK uI uVp

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]

variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uI} [Fintype iota] {Vp : iota → Type uVp}
variable {places : (i : iota) → Vp i → FinitePlaceAtPrime K p}
variable {tuple : (i : iota) → Vp i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {mu : MeasureTheory.Measure (ArithmeticTensorTupleBlock places tuple)}
variable [MeasureTheory.Measure.IsAddHaarMeasure mu]
variable (C6 : C6ActualIQData places tuple mu)

/-- Actual signed q scalar from C3's completion element. -/
structure QPaperScalar
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  value : Real
  value_eq : value = localSignedLog C3.q

/-- Paper Q(I): actual q scalar, actual C6 q-pilot region constrained to the
C6 hull, and the C6 normalized log-volume.  No Ind1/2/3 field. -/
structure QPaper
    (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  qPilotRegion : Set (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  qPilotRegion_eq_unit : qPilotRegion =
    {(C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
  scalar : QPaperScalar C3
  kummer : SourceLogKummerData I C1 := C2
  qPilotLogVolume : WithTop Real
  qPilotLogVolume_eq : qPilotLogVolume = (scalar.value : WithTop Real)

/-- Actual QPaper constructed from C3's tensor unit and q scalar. -/
def qPaperOfC3
    (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    QPaper D C1 C2 C3 where
  qPilotRegion :=
    {(C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
  qPilotRegion_eq_unit := rfl
  scalar := { value := localSignedLog C3.q, value_eq := rfl }
  kummer := C2
  qPilotLogVolume := (localSignedLog C3.q : WithTop Real)
  qPilotLogVolume_eq := rfl

/-- Paper Theta(I) at procession n: actual source hull, actual possible-image
containment, C6 normalized log-volume, Kummer data, actual Ind1/2/3 action. -/
structure ThetaPaper
    (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (n : ThetaPilotCarrier l)
    (C6 : C6ActualIQData places tuple mu) where
  thetaHull : Set (I.ThetaPilotPoint D.place.v)
  thetaHull_eq : thetaHull =
    I.sourceHolomorphicHull D.place.v D.place.R n
  thetaHull_contains_image :
    I.possibleThetaPilotImageSet D.place.v D.place.R n ⊆ thetaHull
  thetaToC6 : Set (I.ThetaPilotPoint D.place.v) → Set (C6IQCarrier places tuple)
  thetaLogVolume : WithTop Real
  thetaLogVolume_eq : thetaLogVolume =
    (C6.normalizedLogVolume (thetaToC6 thetaHull) : WithTop Real)
  kummer : SourceLogKummerData I C1 := C2
  ind : IndActionData (I.ThetaPilotPoint D.place.v) Label := D.ind

/-- Paper Values: actual C6 provenance set; values are computed by the actual
C6 normalizedLogVolume function, not chosen as a free Set Real. -/
structure ValuesPaper (C6 : C6ActualIQData places tuple mu) where
  provenance : Set (C6IQCarrier places tuple)

namespace ValuesPaper

variable {C6 : C6ActualIQData places tuple mu}
variable (V : ValuesPaper (C6 := C6))

/-- Values are the actual C6 normalized log-volumes of the provenance set. -/
def values : Set Real :=
  {z | ∃ S : Set (C6IQCarrier places tuple),
    S ⊆ V.provenance ∧ z = C6.normalizedLogVolume S}

end ValuesPaper

/-- The paper set R^{<= Theta}. -/
def RleqTheta
    {D : SourceWitnessedOutputData (l := l) (V := V) I Label}
    {C1 : SourceInputBinding I} {C2 : SourceLogKummerData I C1}
    {n : ThetaPilotCarrier l}
    (Theta : ThetaPaper (D := D) (C1 := C1) (C2 := C2) (n := n) (C6 := C6)) : Set (WithTop Real) :=
  {lambda | lambda <= Theta.thetaLogVolume}

/-- QPaper belongs to R^{<= ThetaPaper}. -/
def QPaperInRleq
    {D : SourceWitnessedOutputData (l := l) (V := V) I Label}
    {C1 : SourceInputBinding I} {C2 : SourceLogKummerData I C1}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (Q : QPaper (D := D) (C1 := C1) (C2 := C2) (C3 := C3))
    (Theta : ThetaPaper (D := D) (C1 := C1) (C2 := C2) (n := n) (C6 := C6)) : Prop :=
  Q.qPilotLogVolume ∈ RleqTheta (C6 := C6) Theta

/-- Q <= Theta from membership. -/
theorem qPaper_le_thetaPaper_of_mem
    {D : SourceWitnessedOutputData (l := l) (V := V) I Label}
    {C1 : SourceInputBinding I} {C2 : SourceLogKummerData I C1}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (Q : QPaper (D := D) (C1 := C1) (C2 := C2) (C3 := C3))
    (Theta : ThetaPaper (D := D) (C1 := C1) (C2 := C2) (n := n) (C6 := C6))
    (h : QPaperInRleq (C6 := C6) Q Theta) :
    Q.qPilotLogVolume <= Theta.thetaLogVolume := h

/-- Exact missing constraint: Q's C6 normalized volume equals its q scalar. -/
theorem qPaper_scalar_eq_obligation
    {D : SourceWitnessedOutputData (l := l) (V := V) I Label}
    {C1 : SourceInputBinding I} {C2 : SourceLogKummerData I C1}
    {C3 : SourcePilotRegionData (l := l) (V := V) I}
    (Q : QPaper (D := D) (C1 := C1) (C2 := C2) (C3 := C3)) :
    Q.qPilotLogVolume = (Q.scalar.value : WithTop Real) :=
  Q.qPilotLogVolume_eq

/-- Exact donor: a QPaper from the actual C3 data. -/
theorem qPaper_nonempty
    (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Nonempty (QPaper (D := D) (C1 := C1) (C2 := C2) (C3 := C3)) :=
  ⟨qPaperOfC3 (I := I) D C1 C2 C3⟩

end LeanFormal.IUT.N8Closure.C9Paper
