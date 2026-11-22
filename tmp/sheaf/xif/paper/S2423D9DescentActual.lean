import tmp.sheaf.xif.paper.S2158QStackActual
import tmp.sheaf.xif.paper.S2134D9DescentActual
import tmp.sheaf.xif.paper.S2103D9PrestackActual
import tmp.sheaf.xif.paper.S2029GiraudStackificationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2423D9DescentActual

open LeanFormal.IUT.XiFPaper.S2158QStackActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open CategoryTheory

/-- Prestack half for the actual pointwise-colimit Q. -/
def S2423QPrestackRequired : Prop :=
  S2158QPrestack

/-- Effective descent half for Q. -/
def S2423QEffectiveDescentRequired (l : PrimeGeFive) : Prop :=
  S2158QEffectiveDescent l

/-- The concrete hom-presheaf sheaf condition is equivalent to prestack. -/
theorem S2423QPrestack_iff_homSheaf :
    S2423QPrestackRequired ↔ S2158QHomSheaf :=
  S2158QPrestack_iff_homSheaf

/-- Actual Q-stack assembly from the prestack and effective-descent halves. -/
theorem S2423QIsStack_of_components (l : PrimeGeFive)
    (hP : S2423QPrestackRequired)
    (hD : S2423QEffectiveDescentRequired l) :
    S2152QIsStack :=
  (S2158QRequiredAPI_iff_isStack l).mp
    ⟨⟨hP, hD⟩⟩

/-- Exact first missing for the Q route: the two concrete halves. -/
def S2423QFirstMissing (l : PrimeGeFive) : Prop :=
  S2158ConcreteFirstMissing l

/-- The Q first missing is the API. -/
theorem S2423QFirstMissing_iff_API (l : PrimeGeFive) :
    S2423QFirstMissing l ↔ Nonempty (S2158QRequiredAPI l) :=
  S2158ConcreteFirstMissing_iff l

/-- The D9 slice-sheaf effective-descent first missing. -/
def S2423D9SliceFirstMissing : Prop :=
  S2134FirstMissing (K := S1726K)

/-- Actual base case: on the identity etale cover the slice-sheaf prestack has
effective descent. -/
theorem S2423D9Slice_identity_effectiveDescent
    (S : Iut.SchemeOverField S1726K) :
    HasEffectiveDescentPresieve (S2029SheafPrestack S1726K)
      (Presieve.singleton (𝟙 S)) :=
  (S2134EffDescent_identityCover S).2

/-- Exact first missing in the combined D9 form: the Q stack halves or the
slice-sheaf effective-descent half. -/
def S2423ExactFirstMissing (l : PrimeGeFive) : Prop :=
  S2423QFirstMissing l ∨ S2423D9SliceFirstMissing

end LeanFormal.IUT.XiFPaper.S2423D9DescentActual

end
