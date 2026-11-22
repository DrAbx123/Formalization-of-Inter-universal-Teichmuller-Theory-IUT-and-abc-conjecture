import tmp.sheaf.xif.paper.Mzk1Lemma22StatementShapeActual
import tmp.sheaf.xif.paper.Mzk1Lemma22InductionActual
import Mathlib.Tactic

/-! # Mzk1Lemma22GChoiceDataActual — [Mzk1] Lemma 2.2 g-choice: conditional step packaging

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (apply Lemma 2.1 to lambda*S with suitable
positive rational lambda; f+f0 determines the step); Mzk1Lemma21dAssemblyActual (Lemma 2.1(a)-(d)
PROVED), Mzk1Lemma22StepConstructionActual (stepxi: card collapse card_image_lt_of_collision,
stepOfPoly/stepExists_packaged GREEN 11968), Mzk1PolyMapActual, Mzk1Lemma22CompositionActual,
Mzk1Lemma22InductionActual, Mzk1Lemma22StatementShapeActual.

THIS FILE packages the g-choice data: the two points (0 and alpha2) that collapse under g,
the separation of beta, and the resulting InductionStep.  The CONSTRUCTION of the data
(lambda, m,n, g=f+f0, avoids, unramified from Lemma 2.1) is the remaining obligation,
recorded in rows; no fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CompositionActual

/-- Data of one g-choice (Lemma 2.1 applied to lambda*S): a rational polynomial g
collapsing 0 and alpha2, whose image set is the new target and whose map avoids beta and
is unramified over the complement of the image. -/
structure Mzk1GChoiceData where
  S : Finset (P1Point ℚ)
  beta : P1Point ℚ
  g : ℚ[X]
  hdeg : 1 ≤ g.natDegree
  hcard : (S.image (polyMapPoints g)).card < S.card
  havoids : AvoidsPoint (polyMorphism g hdeg) beta
    (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ))
  hunram : UnramifiedOver (polyMorphism g hdeg)
    {p | p ∉ (↑(S.image (polyMapPoints g)) : Set (P1Point ℚ))} (polyUnramifiedAt g)

/-- Package g-choice data as an induction step: source = S, targetS = image g, phi = the
polynomial map, targetSet = image g (so htarget is rfl). -/
def gChoiceStep (D : Mzk1GChoiceData) : Mzk1Lemma22InductionStep ℚ where
  source := D.S
  targetS := D.S.image (polyMapPoints D.g)
  beta := D.beta
  beta' := polyMapPoints D.g D.beta
  phi := polyMorphism D.g D.hdeg
  targetSet := (↑(D.S.image (polyMapPoints D.g)) : Set (P1Point ℚ))
  unramifiedAt := polyUnramifiedAt D.g
  card_lt := D.hcard
  preserves := by
    intro p hp
    show polyMapPoints D.g p ∈ (↑(D.S.image (polyMapPoints D.g)) : Set (P1Point ℚ))
    exact Finset.mem_image_of_mem (polyMapPoints D.g) hp
  avoids := D.havoids
  beta'_eq := rfl
  unramified := D.hunram

/-- The packaged step satisfies the exact stepExists shape consumed by the induction. -/
theorem gChoiceStep_exists (D : Mzk1GChoiceData) :
    ∃ st : Mzk1Lemma22InductionStep ℚ,
      st.source = D.S ∧ st.beta = D.beta ∧
      st.targetSet = (↑st.targetS : Set (P1Point ℚ)) :=
  ⟨gChoiceStep D, rfl, rfl, rfl⟩

/-- Obligation rows: the constructive g-choice from Lemma 2.1 (the remaining paper step). -/
structure Mzk1GChoiceRow where
  item : String
  status : String
  proved : Bool

def mzk1GChoiceRows : List Mzk1GChoiceRow :=
  [ ⟨"packaging g-choice data as InductionStep", "PROVED (this file)", true⟩,
    ⟨"stepExists instance from g-choice data", "PROVED (gChoiceStep_exists)", true⟩,
    ⟨"choose lambda = 1/alpha2 (second smallest positive point) so lambda*S satisfies Lemma 2.1 (i)-(iii)", "PENDING (finite-set selection + scaling)", false⟩,
    ⟨"construct g = X^m (X-1)^n + f0 in Q[X] with rational f0 (lambda*S rational)", "PENDING", false⟩,
    ⟨"collapse card: g(0) = g(alpha2) via f(0)=f(1)=0", "PENDING (uses Mzk1Lemma22StepConstructionActual.card_image_lt_of_collision)", false⟩,
    ⟨"avoids: g(beta) notin image from Lemma 2.1(c) with lambda beta", "PENDING (uses Mzk1Lemma21ImageActual)", false⟩,
    ⟨"unramified: g'(x) != 0 off image from root dichotomy Mzk1Lemma21Actual", "PENDING", false⟩ ]

theorem mzk1GChoiceRows_length : mzk1GChoiceRows.length = 7 := rfl

#check Mzk1GChoiceData
#check gChoiceStep
#check gChoiceStep_exists
#check mzk1GChoiceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceDataActual
end
