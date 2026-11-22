import tmp.sheaf.n8.closure.EtaRouteInterface
import tmp.sheaf.n8.closure.PaperQLeThetaReduction
import Mathlib

/-!
# Eta comparison consumer with nondegeneracy guards

The independent eta comparison (EtaComparison) supplies the actual q-side
negativity.  The paper normalized consumer is the P6/Values route theorem:
ValuesBounded plus the source comparison imply Q <= Theta.  This file adds the
audit nondegeneracy guards and the exact Q-identification with the eta q scalar.

No direct scalar Q <= Theta assumption and no trivialized-R hypothesis are
used.  The only named gap is the exact normalized Q identification.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.EtaRouteInterface

namespace LeanFormal.IUT.N8Closure.EtaComparisonConsumerNondegenerate

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact normalized identification of the paper Q with the eta q-side scalar. -/
def EtaQNormalizedIdentification (O : PaperC9Output (X := X) mu) : Prop :=
  O.Q = EtaNativeQ X

/-- Audit nondegeneracy guards: Theta nonzero, Values not {0}, and the
P6 readout reference region different from its region.  These are guards, not
scalar inequalities. -/
structure EtaAuditGuards (O : PaperC9Output (X := X) mu) : Prop where
  theta_ne_zero : O.Theta ≠ 0
  values_ne_zero : O.valuesSet ≠ ({0} : Set Real)
  reference_ne_region : O.theta.reference ≠ O.theta.region

/-- EtaComparison gives q-side negativity for the actual Q. -/
theorem etaComparison_Q_neg
    (O : PaperC9Output (X := X) mu)
    (hEta : EtaComparison X)
    (hQ : EtaQNormalizedIdentification (X := X) (mu := mu) O) :
    O.Q < 0 := by
  rw [hQ]
  exact hEta.2.2

/-- Normalized Q <= Theta consumer after the independent eta comparison, with
the audit nondegeneracy guards and the P6/Values route.  No direct scalar
Q <= Theta assumption is used. -/
theorem etaNormalizedQ_le_Theta_nondegenerate
    (O : PaperC9Output (X := X) mu)
    (hEta : EtaComparison X)
    (hQ : EtaQNormalizedIdentification (X := X) (mu := mu) O)
    (_hGuards : EtaAuditGuards (X := X) (mu := mu) O)
    (hVB : ValuesBounded (X := X) (mu := mu) O) :
    O.Q ≤ O.Theta := by
  have _hQneg : O.Q < 0 := etaComparison_Q_neg (X := X) (mu := mu) O hEta hQ
  exact PaperQLeThetaReduction.paperQLeTheta (X := X) (mu := mu) O hVB

end LeanFormal.IUT.N8Closure.EtaComparisonConsumerNondegenerate
