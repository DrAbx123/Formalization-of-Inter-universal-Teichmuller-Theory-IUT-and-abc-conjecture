import tmp.sheaf.xif.paper.GenEll02bProofActual
import tmp.sheaf.xif.paper.GenEll03Prop16Actual
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.GenEll03bProofActual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual
open LeanFormal.IUT.XiFPaper.GenEll02bProofActual
open LeanFormal.IUT.XiFPaper.GenEll03Prop16Actual

/-- **Prop 1.6 proved (elementary direction)**: the pointwise bound
logCondD x <= htD x + C on U(Q) (what the paper's proof supplies: bounded |s| on the
compact archimedean part and Def 1.5(iv) at the nonarchimedean primes) yields the
conductor-bounded-by-height BD relation. -/
theorem prop16_of_pointwise_bound {X : Type} {UQ : Set X} {logCondD htD : X → Real}
    (h : ∃ C : Real, ∀ x ∈ UQ, logCondD x ≤ htD x + C) :
    Prop16ConductorBoundedByHeight UQ logCondD htD :=
  isBDLe_of_le_add_const h

def s3135Prop16ProofCitations : List (String × String) :=
  [ ("Prop 1.6 proof", "corpus 517-523: nonarchimedean from Def 1.5(iv) (reduced divisor), archimedean from bounded continuous |s| on compact X_arc; encoded as the pointwise bound input") ]

theorem s3135Prop16ProofCitations_length : s3135Prop16ProofCitations.length = 1 := rfl

#check prop16_of_pointwise_bound
end LeanFormal.IUT.XiFPaper.GenEll03bProofActual
end
