import tmp.sheaf.n8.closure.C6ActualEllOutLeTheta
import tmp.sheaf.n8.closure.EtaConsumerIndependent
import tmp.sheaf.n8.closure.EtaActualComparisonDivisorAttempt
import Mathlib

/-!
# Paper P6 assembly

`PaperP6Input` bundles the paper-qualified source data (SourceDefinition31Data
with native arithmetic equality), the actual O2 comparison interface, actual O3
comparison-divisor data, and actual O4 C6 output data.  It contains no Q<=Theta
conclusion.  `PaperP6GuardInput` bundles exactly the guard-cone inputs for the
independent consumer.  The `paperP6` skeleton combines the actual C6
h<=Theta bound with the guard consumer Q<=Theta; neither inequality is a field
of either input.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C6ConstructedOutput
open LeanFormal.IUT.N8Closure.C6ActualEllOutLeTheta
open LeanFormal.IUT.N8Closure.EtaActualComparisonDivisorAttempt
open LeanFormal.IUT.N8Closure.EtaConsumerIndependent
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.C9PaperClosure

namespace LeanFormal.IUT.N8Closure.PaperP6Assembly

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Abstract paper initial Theta data interface.  It is intentionally not bound
to the shell `SourceDefinition31Data`; the transport conversion is pending. -/
structure PaperInitialThetaData : Type where
  sourceQualified : Prop
  arithmeticLink : Prop

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]


/-- Paper-qualified input and actual O2/O3/O4 interfaces.  No Q<=Theta field. -/
structure PaperP6Input where
  initial : PaperInitialThetaData
  o2 : EtaComparisonIndependent X
  o3 : ActualComparisonDivisorData X
  c6Output : SourceAllowedOutput X
  hullPoss : c6Output.hullPoss
  normalizedLogVolume_actual : C6NormalizedLogVolumeActual X c6Output
  region_positive_finite : C6RegionPositiveFinite X c6Output

/-- Actual C6 h<=Theta from the O4 fields. -/
theorem paperP6_c6_hLeTheta (P : PaperP6Input X) :
    actualEllOut X P.c6Output ≤ actualThetaCandidate X P.c6Output :=
  actualEllOut_le_actualThetaCandidate X P.c6Output P.hullPoss
    P.normalizedLogVolume_actual P.region_positive_finite

/-- Guard-cone inputs for the independent consumer; no Q<=Theta field. -/
structure PaperP6GuardInput
    (O : PaperC9Output (X := X) mu) where
  eta : EtaComparisonIndependent X
  qIdentification : EtaQNormalizedIdentification (X := X) (mu := mu) O
  guards : EtaAuditGuards (X := X) (mu := mu) O
  valuesBounded : ValuesBounded (X := X) (mu := mu) O

/-- Guard consumer Q<=Theta from the actual consumer; no inequality input. -/
theorem paperP6_guard_QLeTheta
    (O : PaperC9Output (X := X) mu) (G : PaperP6GuardInput X mu O) :
    O.Q ≤ O.Theta :=
  etaNormalizedQ_le_Theta_independent (X := X) (mu := mu) O
    G.eta G.qIdentification G.guards G.valuesBounded

/-- Paper P6 skeleton: actual C6 h<=Theta plus guard-consumer Q<=Theta, from
inputs that carry neither inequality as a field. -/
theorem paperP6
    (P : PaperP6Input X) (O : PaperC9Output (X := X) mu)
    (G : PaperP6GuardInput X mu O) :
    actualEllOut X P.c6Output ≤ actualThetaCandidate X P.c6Output ∧
      O.Q ≤ O.Theta :=
  ⟨paperP6_c6_hLeTheta X P, paperP6_guard_QLeTheta X mu O G⟩

end LeanFormal.IUT.N8Closure.PaperP6Assembly