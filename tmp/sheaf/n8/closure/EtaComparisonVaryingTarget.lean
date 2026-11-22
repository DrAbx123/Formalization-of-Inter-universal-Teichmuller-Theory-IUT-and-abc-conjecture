import tmp.sheaf.n8.closure.EtaRssSourceRegionBridge
import tmp.sheaf.n8.closure.C9PaperClosure
import Mathlib

/-!
# Eta comparison varying target

Uses only the actual varying-region Rss carrier from
EtaRssNontrivialActual/EtaRssSourceRegionBridge.  The comparison target and the
Q/Theta calibrations are explicit named gaps.  The conditional consumer uses
the actual open/closed source-region classes and their strict log-volume
readout order; it does not use the fixed-shell Rss or paperQLeTheta.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaRssSourceRegionBridge
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual

namespace LeanFormal.IUT.N8Closure.EtaComparisonVaryingTarget

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

structure EtaComparisonVaryingTarget (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK] where
  etaQ : Rval → Rss (K := K) muK
  etaAnabS : Rval → Rss (K := K) muK
  comparison : ∀ a : Rval, etaQ a = etaAnabS a
  nonconstant : ¬ ∃ c : Rss (K := K) muK, ∀ a : Rval, etaQ a = c

/-- The intended nonconstant eta comparison is an open obligation. A handcrafted
map that merely fills the structure fields is not evidence for the actual
eta_q/eta^anab_S maps; such a proof would be concept substitution. -/
def etaComparisonVaryingTargetObligation (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK] : Prop :=
  Nonempty (EtaComparisonVaryingTarget K muK)

theorem varyingReadout_open_lt_closed (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK] :
    logVolumeReadout (K := K) (mu := muK) (sourceOpenClass (K := K) (mu := muK)) <
      logVolumeReadout (K := K) (mu := muK) (sourceClosedClass (K := K) (mu := muK)) := by
  have hlt : muK (openRegion (K := K) (mu := muK)).carrier <
      muK (closedRegion (K := K) (mu := muK)).carrier :=
    open_mass_lt_closed_mass (K := K) (mu := muK)
  have hpos : 0 < (muK (openRegion (K := K) (mu := muK)).carrier).toReal :=
    ENNReal.toReal_pos (openRegion (K := K) (mu := muK)).pos.ne'
      (openRegion (K := K) (mu := muK)).finite.ne
  have hto : (muK (openRegion (K := K) (mu := muK)).carrier).toReal <
      (muK (closedRegion (K := K) (mu := muK)).carrier).toReal :=
    (ENNReal.toReal_lt_toReal (openRegion (K := K) (mu := muK)).finite.ne
      (closedRegion (K := K) (mu := muK)).finite.ne).2 hlt
  have hlog := Real.log_lt_log hpos hto
  simpa [sourceOpenClass, sourceClosedClass, sourceOpenRegion, sourceClosedRegion,
    logVolumeReadout_mk] using hlog

def EtaVaryingQCalibration (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu) : Prop :=
  O.Q = logVolumeReadout (K := K) (mu := muK) (sourceOpenClass (K := K) (mu := muK))

def EtaVaryingThetaCalibration (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu) : Prop :=
  O.Theta = logVolumeReadout (K := K) (mu := muK) (sourceClosedClass (K := K) (mu := muK))

theorem etaVarying_Q_le_Theta (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu)
    (hQ : EtaVaryingQCalibration (X := X) (mu := mu) K muK O)
    (hTheta : EtaVaryingThetaCalibration (X := X) (mu := mu) K muK O) :
    O.Q ≤ O.Theta := by
  rw [hQ, hTheta]
  exact le_of_lt (varyingReadout_open_lt_closed K muK)

end LeanFormal.IUT.N8Closure.EtaComparisonVaryingTarget
