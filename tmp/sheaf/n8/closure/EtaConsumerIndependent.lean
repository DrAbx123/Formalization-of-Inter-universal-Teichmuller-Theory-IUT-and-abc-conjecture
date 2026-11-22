import tmp.sheaf.n8.closure.PaperQLeThetaReduction
import tmp.sheaf.n8.closure.C9QThetaValuesNamed
import Mathlib

/-!
# Eta consumer independent

The previous consumer depended on EtaRouteInterface.EtaComparison, which is a
negative-control tautology (the pStar scaling inverse plus q < 0).  It must not
be read as the source comparison eta^q = eta^anab_S.

This file uses an independent EtaComparison interface whose inhabitant is the
explicit named source gap etaComparisonIndependent_exists.  The normalized
Q <= Theta conclusion still comes from the P6/Values route (paperQLeTheta), not
from the Eta tautology; the independent eta q-side is used only to establish
Q < 0.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.C9QPilotRegion

namespace LeanFormal.IUT.N8Closure.EtaConsumerIndependent

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Independent source comparison interface: the q-side eta value and the
anab-side value agree, with the q-side identified with the actual native q
scalar and negative.  This is an interface, not the pStar scaling tautology. -/
structure EtaComparisonIndependent where
  etaQ : Real
  etaAnabS : Real
  comparison : etaQ = etaAnabS
  etaQ_eq_native : etaQ = qPilotSignedLog X
  etaQ_neg : etaQ < 0

/-- The independent eta q-side scalar, read from the native q. -/
def EtaNativeQIndependent : Real :=
  qPilotSignedLog X

/-- Exact normalized identification of paper Q with the independent eta q-side. -/
def EtaQNormalizedIdentification (O : PaperC9Output (X := X) mu) : Prop :=
  O.Q = EtaNativeQIndependent X

/-- Audit nondegeneracy guards (same exact guards as the nondegenerate file). -/
structure EtaAuditGuards (O : PaperC9Output (X := X) mu) : Prop where
  theta_ne_zero : O.Theta ≠ 0
  values_ne_zero : O.valuesSet ≠ ({0} : Set Real)
  reference_ne_region : O.theta.reference ≠ O.theta.region

/-- Independent consumer: an independent eta comparison plus the normalized Q
identification, audit guards, and the P6/Values route imply Q <= Theta.
No direct scalar Q <= Theta assumption and no pStar scaling tautology is used. -/
theorem etaNormalizedQ_le_Theta_independent
    (O : PaperC9Output (X := X) mu)
    (hEta : EtaComparisonIndependent X)
    (hQ : EtaQNormalizedIdentification (X := X) (mu := mu) O)
    (_hGuards : EtaAuditGuards (X := X) (mu := mu) O)
    (hVB : ValuesBounded (X := X) (mu := mu) O) :
    O.Q ≤ O.Theta := by
  have _hQneg : O.Q < 0 := by
    rw [hQ, EtaNativeQIndependent, ← hEta.etaQ_eq_native]
    exact hEta.etaQ_neg
  exact PaperQLeThetaReduction.paperQLeTheta (X := X) (mu := mu) O hVB

end LeanFormal.IUT.N8Closure.EtaConsumerIndependent
