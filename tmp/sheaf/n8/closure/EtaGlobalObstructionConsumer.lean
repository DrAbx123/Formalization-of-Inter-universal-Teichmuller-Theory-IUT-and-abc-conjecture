import tmp.sheaf.n8.closure.EtaGlobalObstructionGuard
import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.EtaComparisonVaryingTarget

/-!
# Eta global obstruction consumer

Connects the exact obstruction data to the PaperC9Output Q/Theta consumer (the
same Q/Theta consumer used by EtaComparisonVaryingTarget).  The consumer
inequality Q <= Theta is available only under:

- the consumer guard kappa = 0 or S >= kappa;
- the source bound h <= Theta.

The sharp counterexample shows the unguarded data are consistent with
h <= Theta while Q > Theta, so an unconditional Q <= Theta consumer is not
valid.  No arbitrary global morphism is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGlobalObstructionConsumer

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.EtaGlobalObstructionGuard

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact obstruction witness for a PaperC9Output Q/Theta pair. -/
structure PaperObstructionWitness
    (O : C9PaperClosure.PaperC9Output X mu) where
  data : GlobalObstructionData
  Q_eq : data.Q = O.Q
  Theta_eq : data.Theta = O.Theta

/-- Consumer guard on a paper obstruction witness. -/
def paperConsumerGuard {O : C9PaperClosure.PaperC9Output X mu}
    (W : PaperObstructionWitness X mu O) : Prop :=
  ConsumerGuard W.data

/-- Actual guarded PaperC9Output consumer: guard + source h <= Theta gives
Q <= Theta. -/
theorem paperC9Output_Q_le_Theta_of_guard
    (O : C9PaperClosure.PaperC9Output X mu)
    (W : PaperObstructionWitness X mu O)
    (hg : paperConsumerGuard X mu W) :
    O.Q ≤ O.Theta := by
  rw [← W.Q_eq, ← W.Theta_eq]
  exact global_Q_le_Theta_of_guard W.data hg

/-- The Q/Theta consumer shared with EtaComparisonVaryingTarget: same guarded
paper output conclusion. -/
theorem etaComparisonVaryingTarget_Q_le_Theta_of_guard
    (O : C9PaperClosure.PaperC9Output X mu)
    (W : PaperObstructionWitness X mu O)
    (hg : paperConsumerGuard X mu W) :
    O.Q ≤ O.Theta :=
  paperC9Output_Q_le_Theta_of_guard X mu O W hg

/-- Unguarded consumer principle, using only h <= Theta. -/
def UnguardedPaperQLeTheta : Prop :=
  ∀ D : GlobalObstructionData, D.Q ≤ D.Theta

/-- The unguarded consumer principle is false; sharpCounterexample registers the
counterexample. -/
theorem unguardedPaperQLeTheta_false : ¬ UnguardedPaperQLeTheta := by
  intro h
  have hc := h sharpCounterexample
  norm_num [sharpCounterexample] at hc

/-- h <= Theta alone is insufficient for the consumer conclusion. -/
theorem sourceBound_alone_insufficient :
    ¬ (∀ D : GlobalObstructionData, D.h ≤ D.Theta → D.Q ≤ D.Theta) := by
  intro h
  have hc := h sharpCounterexample (by norm_num [sharpCounterexample])
  norm_num [sharpCounterexample] at hc

/-- The consumer conclusion for the sharp counterexample fails. -/
theorem sharpCounterexample_consumer_failure :
    ¬ (sharpCounterexample.Q ≤ sharpCounterexample.Theta) := by
  norm_num [sharpCounterexample]

end LeanFormal.IUT.N8Closure.EtaGlobalObstructionConsumer
