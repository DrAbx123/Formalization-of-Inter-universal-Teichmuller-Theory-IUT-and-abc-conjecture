import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTIII.Theorem311.SourceLGPMonoidLayer
import tmp.sheaf.xif.paper.S1265SourceInd2Actual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S3139ResidualNonemptyActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual

variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l V)

def capsuleContract_nonempty :=
  sourceProcessionCapsuleContract_nonempty (R := Real) I

def sourceLGPData_nonempty :=
  standardSourceLGPData_nonempty I

def sourceFmodRealEmbeddingGap : Prop :=
  Nonempty (SourceFmodRealEmbedding (I := I))

#print axioms capsuleContract_nonempty
#print axioms sourceLGPData_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1S3139ResidualNonemptyActual