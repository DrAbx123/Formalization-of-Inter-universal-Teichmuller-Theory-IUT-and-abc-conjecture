import tmp.sheaf.xif.paper.S1265SourceInd2Actual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S3139FmodEmbeddingActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual

variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l V)

/-- If the actual Fmod carries an `Algebra Fmod Real` structure (equivalently
a real embedding), then the source real embedding exists. -/
theorem sourceFmodRealEmbedding_nonempty_of_algebra
    (h : Nonempty (Algebra (I.initial.arithmetic.Fmod) Real)) :
    Nonempty (SourceFmodRealEmbedding (I := I)) := by
  letI : Algebra (I.initial.arithmetic.Fmod) Real := Classical.choice h
  exact ⟨algebraMap (I.initial.arithmetic.Fmod) Real⟩

theorem sourceFmodRealEmbedding_nonempty_iff_algebra :
    Nonempty (SourceFmodRealEmbedding (I := I)) ↔
      Nonempty (Algebra (I.initial.arithmetic.Fmod) Real) :=
  (sourceFmodRealScalar_iff (I := I)).symm

def sourceFmodRealEmbeddingGap : Prop :=
  Nonempty (SourceFmodRealEmbedding (I := I))

#print axioms sourceFmodRealEmbedding_nonempty_of_algebra
#print axioms sourceFmodRealEmbedding_nonempty_iff_algebra
end LeanFormal.IUT.XiFPaper.Mzk1S3139FmodEmbeddingActual