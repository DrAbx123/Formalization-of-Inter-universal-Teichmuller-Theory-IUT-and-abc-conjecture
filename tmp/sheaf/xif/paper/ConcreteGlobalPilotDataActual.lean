import tmp.sheaf.xif.paper.GlobalQPilotObjectActual
import tmp.sheaf.xif.paper.C3GaussianThetaPacketActual
import tmp.sheaf.xif.paper.PaperSignedHull
import tmp.sheaf.xif.paper.ThetaHullActual

/-! # Concrete global q-pilot and Theta-pilot scalar data

This file packages the two actual global scalar data available for the concrete
source:

1. q-pilot side: the actual bad qParameter family
     I.initial.reduction.qParameter : I.initial.badPlaces -> Real,
   its finite-support absolute-log divisor, total |log q|, and signed
   q-pilot log-volume -sum_b |log q_b|.

2. Theta-pilot side: the actual Gaussian finite theta packet
     actualGaussianThetaPacket l,
   with q = 1/5 and theta scale j = realThetaValue (1/5) j, and its actual
   global theta log-volume sum_j log(scale j).

The two scalars are actual data.  No inequality or comparison is asserted.  The
q side is indexed by the full actual bad place set, not by a single local q.
No toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteGlobalPilotDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Theta
open LeanFormal.IUT.XiFPaper.GlobalQPilotObjectActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.PaperSignedHull
open LeanFormal.IUT.XiFPaperThetaHull

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual bad qParameter family of the concrete source. -/
noncomputable def concreteBadQFamily : I.initial.badPlaces → Real :=
  globalQParameterFamily I

/-- The actual finite-support absolute-log divisor of the bad q family. -/
noncomputable def concreteBadQAbsLogDivisor : I.initial.badPlaces →₀ Real :=
  globalQAbsLogDivisor I

/-- The actual total |log q| of the bad q family. -/
noncomputable def concreteBadQAbsLogTotal : Real :=
  globalQAbsLogTotal I

/-- The actual q-pilot signed global log-volume. -/
noncomputable def concreteQPilotLogVolume : Real :=
  globalQPilotSignedLog I

/-- The actual q-pilot global log-magnitude |log q|. -/
noncomputable def concreteQPilotLogMagnitude : Real :=
  concreteBadQAbsLogTotal I

/-- The q-pilot magnitude is the negative signed log-volume. -/
theorem concreteQPilotLogMagnitude_eq_neg_logVolume :
    concreteQPilotLogMagnitude I = -concreteQPilotLogVolume I := rfl

/-- The q-pilot global scalar is exactly the source q-pilot signed scalar. -/
theorem concreteQPilotLogVolume_eq_sourceQPilotSignedLog :
    concreteQPilotLogVolume I = sourceQPilotSignedLog I.initial :=
  globalQPilotSignedLog_eq_sourceQPilotSignedLog I

/-- The actual Gaussian theta packet q is 1/5. -/
theorem concreteThetaPacket_q :
    (actualGaussianThetaPacket (l := l)).q = (5 : Real)⁻¹ :=
  actualGaussianThetaPacket_q_eq_inv_five (l := l)

/-- The actual theta scale is the actual realThetaValue at q = 1/5. -/
theorem concreteThetaScale_eq (j : SignedLabel l.value) :
    (actualGaussianThetaPacket (l := l)).scale j =
      realThetaValue ((5 : Real)⁻¹) j.1 := by
  rw [actualGaussianThetaPacket_q_eq_inv_five]
  exact (actualGaussianThetaPacket (l := l)).scale_eq j

/-- The actual Theta-pilot global log-volume: sum of the actual theta-value
logs. -/
noncomputable def concreteThetaPilotLogVolume : Real :=
  (actualGaussianThetaPacket (l := l)).logVolume

/-- The Theta-pilot log-volume is the actual finite theta-value sum. -/
theorem concreteThetaPilotLogVolume_eq_sum :
    concreteThetaPilotLogVolume (l := l) =
      ∑ j : SignedLabel l.value,
        Real.log ((actualGaussianThetaPacket (l := l)).scale j) :=
  (actualGaussianThetaPacket (l := l)).logVolume_eq_sum

/-- The Theta-pilot log-volume in terms of the actual realThetaValue data. -/
theorem concreteThetaPilotLogVolume_eq_realThetaValue :
    concreteThetaPilotLogVolume (l := l) =
      ∑ j : SignedLabel l.value,
        Real.log (realThetaValue ((5 : Real)⁻¹) j.1) := by
  rw [concreteThetaPilotLogVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [concreteThetaScale_eq]

/-- Actual concrete global q-pilot and Theta-pilot scalar data. -/
structure ConcreteGlobalPilotData where
  badQFamily : I.initial.badPlaces → Real
  badQFamily_eq : badQFamily = concreteBadQFamily I
  badQAbsLogDivisor : I.initial.badPlaces →₀ Real
  badQAbsLogDivisor_eq : badQAbsLogDivisor = concreteBadQAbsLogDivisor I
  qAbsLogTotal : Real
  qAbsLogTotal_eq : qAbsLogTotal = concreteBadQAbsLogTotal I
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = concreteQPilotLogVolume I
  localThetaPacket : FiniteThetaPacket l
  localThetaPacket_eq : localThetaPacket = actualGaussianThetaPacket (l := l)
  localThetaLogVolume : Real
  localThetaLogVolume_eq : localThetaLogVolume = concreteThetaPilotLogVolume (l := l)

/-- The actual concrete global pilot data from the actual bad q family and the
actual Gaussian theta packet. -/
noncomputable def concreteGlobalPilotData : ConcreteGlobalPilotData I where
  badQFamily := concreteBadQFamily I
  badQFamily_eq := rfl
  badQAbsLogDivisor := concreteBadQAbsLogDivisor I
  badQAbsLogDivisor_eq := rfl
  qAbsLogTotal := concreteBadQAbsLogTotal I
  qAbsLogTotal_eq := rfl
  qPilotLogVolume := concreteQPilotLogVolume I
  qPilotLogVolume_eq := rfl
  localThetaPacket := actualGaussianThetaPacket (l := l)
  localThetaPacket_eq := rfl
  localThetaLogVolume := concreteThetaPilotLogVolume (l := l)
  localThetaLogVolume_eq := rfl

/-- Projection: the q-side family is indexed by all actual bad places. -/
theorem concreteGlobalPilotData_badQFamily
    (b : I.initial.badPlaces) :
    (concreteGlobalPilotData I).badQFamily b =
      I.initial.reduction.qParameter b := rfl

/-- Projection: the q-pilot finite support is the actual bad q divisor. -/
theorem concreteGlobalPilotData_badQAbsLogDivisor :
    (concreteGlobalPilotData I).badQAbsLogDivisor =
      ∑ b : I.initial.badPlaces,
        Finsupp.single b |Real.log (I.initial.reduction.qParameter b)| := rfl

/-- Projection: the q-pilot scalar is the source signed q scalar. -/
theorem concreteGlobalPilotData_qPilotLogVolume :
    (concreteGlobalPilotData I).qPilotLogVolume =
      sourceQPilotSignedLog I.initial :=
  concreteQPilotLogVolume_eq_sourceQPilotSignedLog I

/-- Projection: the theta packet is the actual Gaussian packet. -/
theorem concreteGlobalPilotData_localThetaPacket :
    (concreteGlobalPilotData I).localThetaPacket =
      actualGaussianThetaPacket (l := l) := rfl

/-- The actual global q-pilot collection from the full bad q family. -/
noncomputable def globalQPilotCollectionActual :
    GlobalQPilotCollection I :=
  globalQPilotCollection I

/-- The raw sum of the bad q absolute logs.  This is NOT the paper
procession-normalized -|log q| scalar; it is retained only as the underlying
raw magnitude input to the actual procession normalization. -/
noncomputable def globalQPilotRawAbsLogSum : Real :=
  concreteQPilotLogMagnitude I

/-- UNIFORM canonical-procession PROTOTYPE, not the paper scalar: the canonical
uniform signed-label procession average of the q-pilot log-volume copies. The
paper Remark 3.1.1(ii) uses K_v/(F_mod)_v normalized weights, which are not
the uniform 1/card(SignedLabel) weights. -/
noncomputable def canonicalProcessionPrototypeQPilotLogVolume : Real :=
  (canonicalProcession l).average
    (fun _ : SignedLabel l.value =>
      (globalQPilotCollection I).signedLogVolume)

/-- The uniform canonical-procession prototype is a weighted average with
uniform weights; it is not the Remark 3.1.1(ii) paper normalization. -/
theorem canonicalProcessionPrototypeQPilotLogVolume_eq_signed :
    canonicalProcessionPrototypeQPilotLogVolume I =
      (globalQPilotCollection I).signedLogVolume :=
  (canonicalProcession l).average_const
    ((globalQPilotCollection I).signedLogVolume)

/-- The uniform canonical-procession prototype magnitude (paper sign). This is
NOT the paper -|log q| scalar. -/
noncomputable def canonicalProcessionPrototypeQPilotLogMagnitude : Real :=
  -canonicalProcessionPrototypeQPilotLogVolume I

/-- The source-theater LOCAL theta packet data: the actual Gaussian packet with
q = 1/5, its actual theta scale values, and its theta log-volume. This is a
local prototype, NOT the paper global Theta-pilot. -/
structure SourceTheaterLocalThetaPacketData where
  localThetaPacket : FiniteThetaPacket l
  localThetaPacket_eq : localThetaPacket = actualGaussianThetaPacket (l := l)
  scale : SignedLabel l.value → Real
  scale_eq : ∀ j, scale j = realThetaValue ((5 : Real)⁻¹) j.1
  logVolume : Real
  logVolume_eq : logVolume =
    ∑ j : SignedLabel l.value, Real.log (scale j)

/-- The source-theater local theta packet data from the actual theta values. -/
noncomputable def sourceTheaterLocalThetaPacketData : SourceTheaterLocalThetaPacketData (l := l) where
  localThetaPacket := actualGaussianThetaPacket (l := l)
  localThetaPacket_eq := rfl
  scale := fun j => realThetaValue ((5 : Real)⁻¹) j.1
  scale_eq := fun _ => rfl
  logVolume := ∑ j : SignedLabel l.value,
    Real.log (realThetaValue ((5 : Real)⁻¹) j.1)
  logVolume_eq := rfl

/-- The source-theater local theta log-volume. -/
noncomputable def sourceTheaterLocalThetaLogVolume : Real :=
  (sourceTheaterLocalThetaPacketData (l := l)).logVolume

/-- The source-theater local theta log-volume is the actual theta-value sum. -/
theorem sourceTheaterLocalThetaLogVolume_eq_sum :
    sourceTheaterLocalThetaLogVolume (l := l) =
      ∑ j : SignedLabel l.value,
        Real.log (realThetaValue ((5 : Real)⁻¹) j.1) := rfl

/-- The actual Remark 3.1.1(ii) paper normalization weights
K_v/(F_mod)_v are not constructed in the frozen tree.  This empty target type
records the exact missing object; it is not the uniform canonical procession. -/
structure PaperProcessionNormalizationWeights : Type

/-- Exact obstruction: no actual Remark 3.1.1(ii) normalization weights are
available, so the true paper -|log q| scalar cannot be constructed here. -/
def PaperProcessionNormalizationWeightsObstruction : Prop :=
  Nonempty PaperProcessionNormalizationWeights

/-- The uniform canonical-procession prototype must not be used as the final
paper scalar. -/
def CanonicalProcessionPrototypeOnly : Prop :=
  PaperProcessionNormalizationWeightsObstruction

/-- LOCAL PROTOTYPE ONLY, not the final global source comparison: the
source-theater local (q = 1/5) theta log-volume versus the uniform canonical
procession prototype magnitude.  Neither side is the paper Remark 3.1.1(ii)
scalar; this definition is only a local prototype.  No inequality is proved or
assumed. -/
def LocalSourceComparisonPrototype : Prop :=
  sourceTheaterLocalThetaLogVolume (l := l) ≤ canonicalProcessionPrototypeQPilotLogMagnitude I

/-- The q-pilot side of the local prototype is the actual collection's signed
log-volume, not a local C3 q. -/
theorem localSourceComparisonPrototype_qPilotSide :
    (globalQPilotCollection I).signedLogVolume =
      sourceQPilotSignedLog I.initial :=
  globalQPilotCollection_signedLogVolume I

end LeanFormal.IUT.XiFPaper.ConcreteGlobalPilotDataActual

end
