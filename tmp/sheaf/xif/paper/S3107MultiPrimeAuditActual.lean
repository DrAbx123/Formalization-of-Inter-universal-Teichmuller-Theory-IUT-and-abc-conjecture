import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3107MultiPrimeAuditActual

variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput.{0,0,0,0,0} l V)

/-- Per rational-prime C3 donor: a donor whose selected residue prime is p. -/
def S3107PerPrimeDonor (p : Nat) : Type 1 :=
  {D : SourcePilotRegionDonors (l := l) (V := V) I // D.p = p}

/-- The source bad-place index by completion rational prime. -/
def S3107DonorIndex (P : SourcePlaceSelection I.initial.arithmetic) : Type :=
  {p : Nat // exists w : NumberField.FinitePlace I.initial.arithmetic.Fmod,
    w ∈ P.V_mod_bad ∧ (completionRationalPrime w).val = p}

/-- S3107 per-rational-prime donor target. -/
def S3107MultiPrimeDonorTarget
    (P : SourcePlaceSelection I.initial.arithmetic) : Prop :=
  forall p : S3107DonorIndex I P,
    Nonempty (S3107PerPrimeDonor (l := l) (V := V) (I := I) p.1)

/-- A family of per-prime donors gives the target. -/
theorem S3107_target_of_family
    (P : SourcePlaceSelection I.initial.arithmetic)
    (D : forall p : S3107DonorIndex I P,
      S3107PerPrimeDonor (l := l) (V := V) (I := I) p.1) :
    S3107MultiPrimeDonorTarget (l := l) (V := V) I P := by
  intro p
  exact ⟨D p⟩

/-- Global product type of the per-prime C3 data: a Pi over the donor index. -/
def S3107GlobalC3Product
    (P : SourcePlaceSelection I.initial.arithmetic) : Type 1 :=
  forall p : S3107DonorIndex I P,
    S3107PerPrimeDonor (l := l) (V := V) (I := I) p.1

/-- Exact global product target: the Pi is inhabited. -/
def S3107GlobalC3ProductTarget
    (P : SourcePlaceSelection I.initial.arithmetic) : Prop :=
  Nonempty (S3107GlobalC3Product (l := l) (V := V) I P)

theorem S3107_globalProductTarget_of_family
    (P : SourcePlaceSelection I.initial.arithmetic)
    (D : S3107GlobalC3Product (l := l) (V := V) I P) :
    S3107GlobalC3ProductTarget (l := l) (V := V) I P :=
  ⟨D⟩

/-- The exact obstruction for a single global tensor block: the tensor block
is tied to one rational prime p, so a multi-prime product cannot be a single
ArithmeticTensorTupleBlock. -/
def S3107SingleBlockObstruction
    (P : SourcePlaceSelection I.initial.arithmetic) : Prop :=
  forall p q : S3107DonorIndex I P, p.1 = q.1

#check S3107PerPrimeDonor
#check S3107DonorIndex
#check S3107MultiPrimeDonorTarget
#check S3107_target_of_family
#check S3107GlobalC3Product
#check S3107GlobalC3ProductTarget
#check S3107_globalProductTarget_of_family
#check S3107SingleBlockObstruction
#print axioms S3107_target_of_family
#print axioms S3107_globalProductTarget_of_family

end LeanFormal.IUT.XiFPaper.S3107MultiPrimeAuditActual
end