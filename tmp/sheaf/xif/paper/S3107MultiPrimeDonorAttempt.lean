import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.xif.paper.S3089CorrectedOriginalInputActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3107MultiPrimeDonorAttempt

variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput l V)

/-- Scheme A: the rational-prime index set actually used by the S2696 bad family. -/
def S3107DonorIndex : Finset Nat := ({(5 : Nat), 2161} : Finset Nat)

/-- A single-prime donor at a given rational prime p. -/
def S3107PerPrimeDonor
    (I : OriginalInput l V) (p : Nat) : Prop :=
  exists D : SourcePilotRegionDonors (l := l) (V := V) I, D.p = p

/-- Scheme A target: one actual donor per rational bad prime. -/
def S3107MultiPrimeDonorTarget (I : OriginalInput l V) : Prop :=
  forall p : Nat, p ∈ S3107DonorIndex ->
    S3107PerPrimeDonor I p

/-- Any single donor gives its own per-prime member. -/
def S3107_perPrime_of_donor
    (I : OriginalInput l V)
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    S3107PerPrimeDonor I D.p :=
  ⟨D, rfl⟩

#check S3107DonorIndex
#check S3107PerPrimeDonor
#check S3107MultiPrimeDonorTarget
#check S3107_perPrime_of_donor

end LeanFormal.IUT.XiFPaper.S3107MultiPrimeDonorAttempt
end