import tmp.sheaf.xif.paper.S3127ForgetfulActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127ForgetfulActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G3ConditionalActual
variable {l : PrimeGeFive}

/-- Explicit raw-mono hypothesis for the forgetful map: this is NOT implied by
    Mono i in S3127FiniteEtaleOverK (object-covering gap). -/
def S3127G3RawMonoHypothesis
    {X Y : S3127FiniteEtaleOverK (l := l)} (i : X ⟶ Y) : Prop :=
  Mono ((S3127KLinearToFiniteEtaleFunctor (l := l)).map i)

/-- Conditional G3: under the raw-mono hypothesis, Example36 G3 applies to the
    raw forgetful map. This does not claim a lift to S3127Cover. -/
theorem S3127G3RawCofan_of_hypothesis
    {X Y : S3127FiniteEtaleOverK (l := l)} (i : X ⟶ Y)
    (h : S3127G3RawMonoHypothesis i) :
    ∃ (Z : FiniteEtaleCover (S1419AffineScheme l))
      (u : Z ⟶ (S3127KLinearToFiniteEtaleFunctor (l := l)).obj Y),
      Nonempty (IsColimit (BinaryCofan.mk
        ((S3127KLinearToFiniteEtaleFunctor (l := l)).map i) u)) := by
  haveI : Mono ((S3127KLinearToFiniteEtaleFunctor (l := l)).map i) := h
  exact finiteEtaleCover_monoInducesIsoOnDirectSummand _

#check S3127G3RawMonoHypothesis
#check S3127G3RawCofan_of_hypothesis
end LeanFormal.IUT.XiFPaper.S3127G3ConditionalActual
end
