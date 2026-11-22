import tmp.sheaf.n8.closure.EtaGlobalObstructionConsumer

/-!
# O5 guarded consumer actual

O5 is the actual guarded consumer: from the obstruction relation and the guard
kappa = 0 or S >= kappa, together with the source bound h <= Theta, conclude the
PaperC9Output Q <= Theta inequality.

No new O3 data and no new local wrapper are introduced.  The only conditional
consumer available uses the existing PaperObstructionWitness, which explicitly
carries the O3/O4 data (h, kappa, S and the Q/Theta identifications).

DECISION: the workspace does not provide actual O3 (h <= Theta) or O4
(kappa/S) data for the PaperC9Output.  Therefore O5 is stopped at the explicit
dependency boundary: there is no unconditional Q <= Theta theorem, and the
guarded consumer can only be instantiated after O3/O4 supply the witness.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.O5GuardedConsumerActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.EtaGlobalObstructionGuard
open LeanFormal.IUT.N8Closure.EtaGlobalObstructionConsumer

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- O5 conditional actual consumer, using only the existing witness type. -/
theorem o5_paperC9Output_Q_le_Theta
    (O : C9PaperClosure.PaperC9Output X mu)
    (W : PaperObstructionWitness X mu O)
    (hg : paperConsumerGuard X mu W) :
    O.Q ≤ O.Theta :=
  paperC9Output_Q_le_Theta_of_guard X mu O W hg

/-- O5 shared with the EtaComparisonVaryingTarget Q/Theta consumer. -/
theorem o5_etaComparisonVaryingTarget_Q_le_Theta
    (O : C9PaperClosure.PaperC9Output X mu)
    (W : PaperObstructionWitness X mu O)
    (hg : paperConsumerGuard X mu W) :
    O.Q ≤ O.Theta :=
  etaComparisonVaryingTarget_Q_le_Theta_of_guard X mu O W hg

/-- The unconditional O5 target. -/
def O5UnconditionalTarget : Prop :=
  ∀ D : GlobalObstructionData, D.Q ≤ D.Theta

/-- Decision: unconditional O5 closure is unavailable. -/
theorem o5_unconditional_closure_unavailable :
    ¬ O5UnconditionalTarget :=
  unguardedPaperQLeTheta_false

/-- h <= Theta alone is insufficient for O5. -/
theorem o5_sourceBound_alone_insufficient :
    ¬ (∀ D : GlobalObstructionData, D.h ≤ D.Theta → D.Q ≤ D.Theta) :=
  sourceBound_alone_insufficient

/-- The sharp counterexample remains the obstruction to unconditional O5. -/
theorem o5_sharpCounterexample_failure :
    ¬ (sharpCounterexample.Q ≤ sharpCounterexample.Theta) :=
  sharpCounterexample_consumer_failure

end LeanFormal.IUT.N8Closure.O5GuardedConsumerActual
