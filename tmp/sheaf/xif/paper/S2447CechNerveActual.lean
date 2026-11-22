import tmp.sheaf.xif.paper.S2445CechActual
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# S2447: the actual Cech nerve of a presieve, its descent data, and the comparison from an
amalgam

S2445 records the Cech-nerve interfaces of the D9 stack problem: the index category
R.category of a presieve R at S, the abstract category of descent data, and the
amalgamation requirement.  It does not construct a Cech nerve, and it does not connect an
amalgam to a Cech descent datum.

This file does that.  For a presieve R at an object S of the etale site
SchemeOverField K = Over (Spec K) we construct, using the actual fiber products of
schemes over K (Mathlib has HasPullbacks Scheme, hence HasPullbacks (Over (Spec K))):

* cechSq i j : ChosenPullback (f i) (f j) and cechSq3 i j k : ChosenPullback3 ...,
  where f i : X i -> S is the arrow of R indexed by i : R.category, and X i is its
  domain.  These are the actual 1- and 2-simplices of the Cech nerve of R.
* the truncation of the Cech nerve: objects in degrees 0, 1, 2, the two projections from a
  1-simplex to its endpoints, the base projection to S, the three face maps from a
  2-simplex to its edges, the degeneracy CechDeg : X i -> P i i, and the truncated
  simplicial identities (CechFace..._eq...).  All of these are ordinary fiber products
  and projection maps; nothing is postulated.
* the Cech descent data CechDescentDatum N = F.DescentData' N.sq N.sq3 of Mathlib's
  chosen-pullback descent category, and the comparison functor
  cechComparison N : F(S) -> CechDescentDatum N, which sends an object M to the descent
  datum whose 0-simplices are the pullbacks of M to the X i and whose 1-simplices are
  the canonical mapComp' comparisons on the chosen pullbacks.
* an amalgam CechAmalgam N D in Cech form (an object of F(S) together with an
  isomorphism from its Cech comparison to D), and actual maps in both directions between
  this and the abstract Amalgam of S2134 (amalgamToCech, cechToAmalgam), proved to
  give an equivalence on nonemptiness.

The exact first missing for the gluing is therefore identified precisely: for a Cech
descent datum D one must produce an object M of the fibre at S together with an
isomorphism cechComparison N M = D.  This is equivalent to effective descent for the
presieve (cechGluing_iff_effectiveDescent), equivalently to S2445's
S2445AmalgamationRequirement (S2447CechGluing_iff_S2445AmalgamationRequirement).
No such construction is provided here for a general proper cover; the file proves the
non-vacuous case in which the generated sieve is maximal
(cechGluing_of_generate_top), and shows the global form is exactly S2445's
S2445AllCechAmalgamation (equivalently S2134's family form of effective descent).

## Honest boundary

No IsStack instance is produced, no amalgam is fabricated for a proper etale cover, and
no axiom beyond propext, Classical.choice, Quot.sound is used.  The file constructs
the Cech nerve and the Cech descent comparison; it does not prove that the comparison is
essentially surjective on a proper cover (that is exactly the named missing below).
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2445CechActual

namespace LeanFormal.IUT.XiFPaper.S2447CechNerveActual

/-! ## 0. Chosen pullbacks from Mathlib's HasPullback -/

section ChosenPullbackData

universe v u

variable {C : Type u} [Category.{v} C]

/-- A chosen pullback, obtained from a HasPullback instance.  This is the only piece of
bookkeeping needed to pass from the existence of fiber products (automatic for schemes
over a field) to the chosen-pullback data used by the Cech nerve. -/
noncomputable def chosenPullbackOfHasPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] : ChosenPullback f₁ f₂ where
  pullback := pullback f₁ f₂
  p₁ := pullback.fst f₁ f₂
  p₂ := pullback.snd f₁ f₂
  condition := pullback.condition
  isLimit := (IsPullback.of_hasPullback f₁ f₂).isLimit

@[simp]
theorem chosenPullbackOfHasPullback_pullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] :
    (chosenPullbackOfHasPullback f₁ f₂).pullback = pullback f₁ f₂ := rfl

@[simp]
theorem chosenPullbackOfHasPullback_p₁ {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] :
    (chosenPullbackOfHasPullback f₁ f₂).p₁ = pullback.fst f₁ f₂ := rfl

@[simp]
theorem chosenPullbackOfHasPullback_p₂ {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] :
    (chosenPullbackOfHasPullback f₁ f₂).p₂ = pullback.snd f₁ f₂ := rfl

@[simp]
theorem chosenPullbackOfHasPullback_p {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] :
    (chosenPullbackOfHasPullback f₁ f₂).p = pullback.fst f₁ f₂ ≫ f₁ := rfl

/-- A chosen triple (wide) pullback from a chosen pullback of the middle pair.  The
witness l of the compatibility with the outer pullback is obtained from the universal
property of that outer pullback; no compatibility is assumed. -/
noncomputable def chosenPullback₃OfHasPullback
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃)
    [HasPullback h₁₂.p₂ h₂₃.p₁] : ChosenPullback₃ h₁₂ h₂₃ h₁₃ := by
  let cp : ChosenPullback h₁₂.p₂ h₂₃.p₁ := chosenPullbackOfHasPullback h₁₂.p₂ h₂₃.p₁
  have hw : cp.p₁ ≫ h₁₂.p = cp.p₂ ≫ h₂₃.p := by
    rw [← h₁₂.hp₂, ← h₂₃.hp₁, ← Category.assoc, ← Category.assoc, cp.hp₁, cp.hp₂]
  have hw' : (cp.p₁ ≫ h₁₂.p₁) ≫ f₁ = (cp.p₂ ≫ h₂₃.p₂) ≫ f₃ := by
    rw [Category.assoc, Category.assoc, h₁₂.hp₁, h₂₃.hp₂]
    exact hw
  have hf₁ : (cp.p₁ ≫ h₁₂.p₁) ≫ f₁ = cp.p₁ ≫ h₁₂.p := by
    rw [Category.assoc, h₁₂.hp₁]
  exact
    { chosenPullback := cp
      p := cp.p₁ ≫ h₁₂.p
      p₁ := cp.p₁ ≫ h₁₂.p₁
      p₃ := cp.p₂ ≫ h₂₃.p₂
      l := Classical.choice (ChosenPullback.LiftStruct.nonempty (h := h₁₃) hw' hf₁)
      hp₁ := rfl
      hp₃ := rfl }

@[simp]
theorem chosenPullback₃OfHasPullback_pullback
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃} {h₁₃ : ChosenPullback f₁ f₃}
    [HasPullback h₁₂.p₂ h₂₃.p₁] :
    (chosenPullback₃OfHasPullback h₁₂ h₂₃ h₁₃).pullback =
      (chosenPullbackOfHasPullback h₁₂.p₂ h₂₃.p₁).pullback := rfl

@[simp]
theorem chosenPullback₃OfHasPullback_p₁
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃} {h₁₃ : ChosenPullback f₁ f₃}
    [HasPullback h₁₂.p₂ h₂₃.p₁] :
    (chosenPullback₃OfHasPullback h₁₂ h₂₃ h₁₃).p₁ =
      (chosenPullbackOfHasPullback h₁₂.p₂ h₂₃.p₁).p₁ ≫ h₁₂.p₁ := rfl

@[simp]
theorem chosenPullback₃OfHasPullback_p₂
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃} {h₁₃ : ChosenPullback f₁ f₃}
    [HasPullback h₁₂.p₂ h₂₃.p₁] :
    (chosenPullback₃OfHasPullback h₁₂ h₂₃ h₁₃).p₂ =
      (chosenPullbackOfHasPullback h₁₂.p₂ h₂₃.p₁).p := rfl

@[simp]
theorem chosenPullback₃OfHasPullback_p₃
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    {h₁₂ : ChosenPullback f₁ f₂} {h₂₃ : ChosenPullback f₂ f₃} {h₁₃ : ChosenPullback f₁ f₃}
    [HasPullback h₁₂.p₂ h₂₃.p₁] :
    (chosenPullback₃OfHasPullback h₁₂ h₂₃ h₁₃).p₃ =
      (chosenPullbackOfHasPullback h₁₂.p₂ h₂₃.p₁).p₂ ≫ h₂₃.p₂ := rfl

end ChosenPullbackData

/-! ## 1. The actual Cech nerve of a presieve -/

section PresieveCech

variable {K : Type} [Field K]

/-- The domain of the arrow of R indexed by i : R.category. -/
def cechFamily (S : Iut.SchemeOverField K) (R : Presieve S) (i : R.category) :
    Iut.SchemeOverField K :=
  i.obj.left

/-- The arrow of R indexed by i : R.category. -/
def cechFamilyHom (S : Iut.SchemeOverField K) (R : Presieve S) (i : R.category) :
    cechFamily (K := K) S R i ⟶ S :=
  i.obj.hom

/-- The 1-simplices of the Cech nerve of a presieve: the actual fiber product over S
of the arrows indexed by i and j. -/
noncomputable def cechSq (S : Iut.SchemeOverField K) (R : Presieve S) (i j : R.category) :
    ChosenPullback (cechFamilyHom (K := K) S R i) (cechFamilyHom (K := K) S R j) :=
  chosenPullbackOfHasPullback _ _

/-- The 2-simplices of the Cech nerve of a presieve: the actual triple fiber product
over S of the arrows indexed by i, j, k. -/
noncomputable def cechSq₃ (S : Iut.SchemeOverField K) (R : Presieve S)
    (i j k : R.category) :
    ChosenPullback₃ (cechSq (K := K) S R i j) (cechSq (K := K) S R j k)
      (cechSq (K := K) S R i k) :=
  chosenPullback₃OfHasPullback _ _ _

/-- The Cech-nerve data of a presieve: actual chosen pullbacks for every pair of arrows
and actual chosen triple pullbacks for every triple. -/
structure CechNerveData (S : Iut.SchemeOverField K) (R : Presieve S) where
  /-- chosen fiber products of pairs of arrows of R over S -/
  sq : ∀ i j : R.category,
    ChosenPullback (cechFamilyHom (K := K) S R i) (cechFamilyHom (K := K) S R j)
  /-- chosen triple fiber products of triples of arrows of R over S -/
  sq₃ : ∀ i j k : R.category, ChosenPullback₃ (sq i j) (sq j k) (sq i k)

/-- The Cech-nerve data produced by the actual fiber products of schemes over K. -/
noncomputable def cechNerveData (S : Iut.SchemeOverField K) (R : Presieve S) :
    CechNerveData (K := K) S R where
  sq := cechSq (K := K) S R
  sq₃ := cechSq₃ (K := K) S R

/-- The 0-simplices of the Cech nerve: the domains of the arrows of R. -/
abbrev CechZero (S : Iut.SchemeOverField K) (R : Presieve S) (i : R.category) :
    Iut.SchemeOverField K :=
  cechFamily (K := K) S R i

/-- The object of the Cech nerve in degree 1 at the pair (i,j): the fiber product
X i x_S X j. -/
abbrev CechOne (S : Iut.SchemeOverField K) (R : Presieve S) (N : CechNerveData (K := K) S R)
    (i j : R.category) : Iut.SchemeOverField K :=
  (N.sq i j).pullback

/-- The object of the Cech nerve in degree 2 at the triple (i,j,k): the triple fiber
product X i x_S X j x_S X k. -/
abbrev CechTwo (S : Iut.SchemeOverField K) (R : Presieve S) (N : CechNerveData (K := K) S R)
    (i j k : R.category) : Iut.SchemeOverField K :=
  (N.sq₃ i j k).pullback

/-- First projection of a 1-simplex. -/
abbrev CechOneFst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j : R.category) :
    CechOne (K := K) S R N i j ⟶ CechZero (K := K) S R i :=
  (N.sq i j).p₁

/-- Second projection of a 1-simplex. -/
abbrev CechOneSnd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j : R.category) :
    CechOne (K := K) S R N i j ⟶ CechZero (K := K) S R j :=
  (N.sq i j).p₂

/-- Base projection of a 1-simplex to S. -/
abbrev CechOneBase (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j : R.category) :
    CechOne (K := K) S R N i j ⟶ S :=
  (N.sq i j).p

/-- First projection of a 2-simplex to X i. -/
abbrev CechTwoFst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ CechZero (K := K) S R i :=
  (N.sq₃ i j k).p₁

/-- Second projection of a 2-simplex to X j. -/
abbrev CechTwoSnd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ CechZero (K := K) S R j :=
  (N.sq₃ i j k).p₂

/-- Third projection of a 2-simplex to X k. -/
abbrev CechTwoThd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ CechZero (K := K) S R k :=
  (N.sq₃ i j k).p₃

/-- Base projection of a 2-simplex to S. -/
abbrev CechTwoBase (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ S :=
  (N.sq₃ i j k).p

/-- The face map from a 2-simplex (i,j,k) to its edge (i,j). -/
abbrev CechFace₁₂ (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ CechOne (K := K) S R N i j :=
  (N.sq₃ i j k).p₁₂

/-- The face map from a 2-simplex (i,j,k) to its edge (j,k). -/
abbrev CechFace₂₃ (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ CechOne (K := K) S R N j k :=
  (N.sq₃ i j k).p₂₃

/-- The face map from a 2-simplex (i,j,k) to its edge (i,k). -/
abbrev CechFace₁₃ (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwo (K := K) S R N i j k ⟶ CechOne (K := K) S R N i k :=
  (N.sq₃ i j k).p₁₃

/-- The degeneracy of a 0-simplex i into the 1-simplex (i,i), given by the diagonal
of the chosen pullback. -/
noncomputable def CechDeg (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i : R.category) :
    CechZero (K := K) S R i ⟶ CechOne (K := K) S R N i i :=
  (Classical.choice (inferInstance : Nonempty (N.sq i i).Diagonal)).f

/-! ### Well-definedness of the Cech projections -/

@[reassoc (attr := simp)]
theorem CechOneFst_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j : R.category) :
    CechOneFst (K := K) S R N i j ≫ cechFamilyHom (K := K) S R i =
      CechOneBase (K := K) S R N i j :=
  (N.sq i j).hp₁

@[reassoc (attr := simp)]
theorem CechOneSnd_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j : R.category) :
    CechOneSnd (K := K) S R N i j ≫ cechFamilyHom (K := K) S R j =
      CechOneBase (K := K) S R N i j :=
  (N.sq i j).hp₂

@[reassoc (attr := simp)]
theorem CechTwoFst_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwoFst (K := K) S R N i j k ≫ cechFamilyHom (K := K) S R i =
      CechTwoBase (K := K) S R N i j k :=
  (N.sq₃ i j k).w₁

@[reassoc (attr := simp)]
theorem CechTwoSnd_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwoSnd (K := K) S R N i j k ≫ cechFamilyHom (K := K) S R j =
      CechTwoBase (K := K) S R N i j k :=
  (N.sq₃ i j k).w₂

@[reassoc (attr := simp)]
theorem CechTwoThd_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechTwoThd (K := K) S R N i j k ≫ cechFamilyHom (K := K) S R k =
      CechTwoBase (K := K) S R N i j k :=
  (N.sq₃ i j k).w₃

@[reassoc (attr := simp)]
theorem CechFace₁₂_fst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₂ (K := K) S R N i j k ≫ CechOneFst (K := K) S R N i j =
      CechTwoFst (K := K) S R N i j k :=
  (N.sq₃ i j k).p₁₂_p₁

@[reassoc (attr := simp)]
theorem CechFace₁₂_snd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₂ (K := K) S R N i j k ≫ CechOneSnd (K := K) S R N i j =
      CechTwoSnd (K := K) S R N i j k :=
  (N.sq₃ i j k).p₁₂_p₂

@[reassoc (attr := simp)]
theorem CechFace₂₃_fst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₂₃ (K := K) S R N i j k ≫ CechOneFst (K := K) S R N j k =
      CechTwoSnd (K := K) S R N i j k :=
  (N.sq₃ i j k).p₂₃_p₂

@[reassoc (attr := simp)]
theorem CechFace₂₃_snd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₂₃ (K := K) S R N i j k ≫ CechOneSnd (K := K) S R N j k =
      CechTwoThd (K := K) S R N i j k :=
  (N.sq₃ i j k).p₂₃_p₃

@[reassoc (attr := simp)]
theorem CechFace₁₃_fst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₃ (K := K) S R N i j k ≫ CechOneFst (K := K) S R N i k =
      CechTwoFst (K := K) S R N i j k :=
  (N.sq₃ i j k).p₁₃_p₁

@[reassoc (attr := simp)]
theorem CechFace₁₃_snd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₃ (K := K) S R N i j k ≫ CechOneSnd (K := K) S R N i k =
      CechTwoThd (K := K) S R N i j k :=
  (N.sq₃ i j k).p₁₃_p₃

@[reassoc (attr := simp)]
theorem CechFace₁₂_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₂ (K := K) S R N i j k ≫ CechOneBase (K := K) S R N i j =
      CechTwoBase (K := K) S R N i j k :=
  (N.sq₃ i j k).p₁₂_p

@[reassoc (attr := simp)]
theorem CechFace₂₃_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₂₃ (K := K) S R N i j k ≫ CechOneBase (K := K) S R N j k =
      CechTwoBase (K := K) S R N i j k :=
  (N.sq₃ i j k).p₂₃_p

@[reassoc (attr := simp)]
theorem CechFace₁₃_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₃ (K := K) S R N i j k ≫ CechOneBase (K := K) S R N i k =
      CechTwoBase (K := K) S R N i j k :=
  (N.sq₃ i j k).p₁₃_p

/-! ### Truncated simplicial identities -/

/-- The two ways around from a 2-simplex to X i agree. -/
theorem CechFace₁₂_fst_eq_CechFace₁₃_fst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₂ (K := K) S R N i j k ≫ CechOneFst (K := K) S R N i j =
      CechFace₁₃ (K := K) S R N i j k ≫ CechOneFst (K := K) S R N i k := by
  rw [CechFace₁₂_fst, CechFace₁₃_fst]

/-- The truncated simplicial identity at the shared middle vertex: the (i,j)-edge and
the (j,k)-edge agree on X j. -/
theorem CechFace₁₂_snd_eq_CechFace₂₃_fst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₁₂ (K := K) S R N i j k ≫ CechOneSnd (K := K) S R N i j =
      CechFace₂₃ (K := K) S R N i j k ≫ CechOneFst (K := K) S R N j k := by
  rw [CechFace₁₂_snd, CechFace₂₃_fst]

/-- The truncated simplicial identity at the last vertex. -/
theorem CechFace₂₃_snd_eq_CechFace₁₃_snd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i j k : R.category) :
    CechFace₂₃ (K := K) S R N i j k ≫ CechOneSnd (K := K) S R N j k =
      CechFace₁₃ (K := K) S R N i j k ≫ CechOneSnd (K := K) S R N i k := by
  rw [CechFace₂₃_snd, CechFace₁₃_snd]

/-! ### Well-definedness of the degeneracy -/

@[reassoc (attr := simp)]
theorem CechDeg_fst (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i : R.category) :
    CechDeg (K := K) S R N i ≫ CechOneFst (K := K) S R N i i =
      𝟙 (CechZero (K := K) S R i) :=
  (Classical.choice (inferInstance : Nonempty (N.sq i i).Diagonal)).f_p₁

@[reassoc (attr := simp)]
theorem CechDeg_snd (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i : R.category) :
    CechDeg (K := K) S R N i ≫ CechOneSnd (K := K) S R N i i =
      𝟙 (CechZero (K := K) S R i) :=
  (Classical.choice (inferInstance : Nonempty (N.sq i i).Diagonal)).f_p₂

@[reassoc (attr := simp)]
theorem CechDeg_base (S : Iut.SchemeOverField K) (R : Presieve S)
    (N : CechNerveData (K := K) S R) (i : R.category) :
    CechDeg (K := K) S R N i ≫ CechOneBase (K := K) S R N i i =
      cechFamilyHom (K := K) S R i :=
  (Classical.choice (inferInstance : Nonempty (N.sq i i).Diagonal)).f_p

end PresieveCech


/-! ## 2. The Cech descent data and the comparison functor -/

section CechDescent

variable {K : Type} [Field K] (S : Iut.SchemeOverField K) (R : Presieve S)

/-- The pseudofunctor of the D9 target: the slice-sheaf prestack over K. -/
def F := S2029SheafPrestack K

/-- The Cech descent data of a presieve, in Mathlib's chosen-pullback descent category:
objects on the 0-simplices, comparison isomorphisms on the 1-simplices, and the
cocycle condition on the 2-simplices. -/
abbrev CechDescentDatum (N : CechNerveData (K := K) S R) : Type _ :=
  F.DescentData' (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R)
    N.sq N.sq₃

/-- The forgetful functor from chosen-pullback Cech descent data back to Mathlib's
abstract descent data. -/
noncomputable def cechToDescent (N : CechNerveData (K := K) S R) :
    CechDescentDatum (K := K) S R N ⥤
      F.DescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R) :=
  Pseudofunctor.DescentData'.toDescentDataFunctor F N.sq N.sq₃

/-- The comparison from abstract descent data to the chosen-pullback Cech descent data. -/
noncomputable def descentToCech (N : CechNerveData (K := K) S R) :
    F.DescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R) ⥤
      CechDescentDatum (K := K) S R N :=
  Pseudofunctor.DescentData'.fromDescentDataFunctor F N.sq N.sq₃

/-- The equivalence between the chosen-pullback Cech descent data and the abstract
descent data.  It is Mathlib's comparison of descent data with chosen pullbacks. -/
noncomputable def cechEquivalence (N : CechNerveData (K := K) S R) :
    CechDescentDatum (K := K) S R N ≌
      F.DescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R) :=
  Pseudofunctor.DescentData'.descentDataEquivalence F N.sq N.sq₃

/-- The Cech descent comparison functor: an object of the fibre at S is sent to the
descent datum obtained by pulling it back to the arrows of R and comparing on the actual
fiber products. -/
noncomputable def cechComparison (N : CechNerveData (K := K) S R) :
    F.obj (.mk (op S)) ⥤ CechDescentDatum (K := K) S R N :=
  (F.toDescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R)) ⋙
    descentToCech (K := K) S R N

/-- The comparison functor is the composite of Mathlib's descent functor with the
chosen-pullback comparison. -/
theorem cechComparison_eq (N : CechNerveData (K := K) S R) :
    cechComparison (K := K) S R N =
      (F.toDescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R)) ⋙
        descentToCech (K := K) S R N := rfl

/-- The 0-simplex of the Cech comparison at M is the pullback of M to the domain of the
arrow of R indexed by i. -/
@[simp]
theorem cechComparison_obj (N : CechNerveData (K := K) S R) (M : F.obj (.mk (op S)))
    (i : R.category) :
    ((cechComparison (K := K) S R N).obj M).obj i =
      (F.map (cechFamilyHom (K := K) S R i).op.toLoc).toFunctor.obj M := rfl

/-- The Cech comparison is functorial on morphisms of the fibre at S. -/
@[simp]
theorem cechComparison_map (N : CechNerveData (K := K) S R) {M M' : F.obj (.mk (op S))}
    (φ : M ⟶ M') (i : R.category) :
    ((cechComparison (K := K) S R N).map φ).hom i =
      (F.map (cechFamilyHom (K := K) S R i).op.toLoc).toFunctor.map φ := rfl

/-- A Cech amalgam for a Cech descent datum D: an actual object M of the fibre at S
together with an isomorphism from its Cech descent comparison to D.  This is the
concrete form of the gluing, expressed on the actual fiber products. -/
structure CechAmalgam (N : CechNerveData (K := K) S R)
    (D : CechDescentDatum (K := K) S R N) where
  /-- the object of the fibre at S that is glued -/
  M : F.obj (.mk (op S))
  /-- the comparison of its Cech descent datum with D -/
  iso : (cechComparison (K := K) S R N).obj M ≅ D

namespace CechAmalgam

variable {S R} {N : CechNerveData (K := K) S R}
  {D₁ D₂ : CechDescentDatum (K := K) S R N}

/-- Change of target for a Cech amalgam. -/
def congr (e : D₁ ≅ D₂) (A : CechAmalgam (K := K) S R N D₁) :
    CechAmalgam (K := K) S R N D₂ where
  M := A.M
  iso := A.iso.trans e

end CechAmalgam

/-- The actual map from an amalgam to the Cech descent comparison.  An amalgam of an
abstract descent datum D produces a Cech amalgam of the chosen-pullback datum induced by
D: the object is the amalgam's object and the comparison is the image of the amalgam's
isomorphism under the chosen-pullback comparison functor. -/
def amalgamToCech {N : CechNerveData (K := K) S R}
    {D : F.DescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R)}
    (A : Amalgam F (cechFamilyHom (K := K) S R) D) :
    CechAmalgam (K := K) S R N ((descentToCech (K := K) S R N).obj D) where
  M := A.M
  iso := (descentToCech (K := K) S R N).mapIso A.iso

/-- The reverse actual comparison.  A Cech amalgam gives an abstract amalgam for the
descent datum obtained by forgetting the chosen pullbacks. -/
def cechToAmalgam {N : CechNerveData (K := K) S R}
    {D : CechDescentDatum (K := K) S R N}
    (A : CechAmalgam (K := K) S R N D) :
    Amalgam F (cechFamilyHom (K := K) S R) ((cechToDescent (K := K) S R N).obj D) where
  M := A.M
  iso := ((cechEquivalence (K := K) S R N).counitIso.app
      ((F.toDescentData (X := cechFamily (K := K) S R)
        (f := cechFamilyHom (K := K) S R)).obj A.M)).symm.trans
    ((cechToDescent (K := K) S R N).mapIso A.iso)

/-- Change of target for an abstract amalgam. -/
def amalgamCongr
    {D₁ D₂ : F.DescentData (X := cechFamily (K := K) S R)
      (f := cechFamilyHom (K := K) S R)}
    (e : D₁ ≅ D₂) (A : Amalgam F (cechFamilyHom (K := K) S R) D₁) :
    Amalgam F (cechFamilyHom (K := K) S R) D₂ where
  M := A.M
  iso := A.iso.trans e

/-- The two amalgam notions have the same nonemptiness on the image of the
chosen-pullback comparison functor. -/
theorem cechAmalgam_nonempty_iff_amalgam_nonempty_image
    (N : CechNerveData (K := K) S R)
    (D : F.DescentData (X := cechFamily (K := K) S R) (f := cechFamilyHom (K := K) S R)) :
    Nonempty (CechAmalgam (K := K) S R N ((descentToCech (K := K) S R N).obj D)) ↔
      Nonempty (Amalgam F (cechFamilyHom (K := K) S R) D) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨amalgamCongr (S := S) (R := R)
      ((cechEquivalence (K := K) S R N).counitIso.app D)
      (cechToAmalgam (S := S) (R := R) A)⟩
  · rintro ⟨A⟩
    exact ⟨amalgamToCech (S := S) (R := R) A⟩

/-- The two amalgam notions have the same nonemptiness for every Cech descent datum. -/
theorem cechAmalgam_nonempty_iff_amalgam_nonempty
    (N : CechNerveData (K := K) S R) (D : CechDescentDatum (K := K) S R N) :
    Nonempty (CechAmalgam (K := K) S R N D) ↔
      Nonempty (Amalgam F (cechFamilyHom (K := K) S R)
        ((cechToDescent (K := K) S R N).obj D)) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨cechToAmalgam (S := S) (R := R) A⟩
  · rintro ⟨A⟩
    exact ⟨CechAmalgam.congr ((cechEquivalence (K := K) S R N).unitIso.app D).symm
      (amalgamToCech (S := S) (R := R) A)⟩

/-- The Cech gluing requirement: every Cech descent datum on the actual Cech nerve of
R admits an amalgam in Cech form.  This is the concrete gluing statement. -/
def CechGluing (N : CechNerveData (K := K) S R) : Prop :=
  ∀ D : CechDescentDatum (K := K) S R N, Nonempty (CechAmalgam (K := K) S R N D)

/-- The Cech gluing requirement is the essential surjectivity of the Cech comparison
functor.  This is the precise first missing: produce, for every descent datum D, an
object M and an isomorphism cechComparison M = D. -/
theorem CechGluing_iff_essSurj (N : CechNerveData (K := K) S R) :
    CechGluing (K := K) S R N ↔ (cechComparison (K := K) S R N).EssSurj := by
  constructor
  · intro h
    refine ⟨fun D => ?_⟩
    obtain ⟨A⟩ := h D
    exact ⟨A.M, ⟨A.iso⟩⟩
  · intro h D
    obtain ⟨M, hM⟩ := h.mem_essImage D
    obtain ⟨e⟩ := hM
    exact ⟨⟨M, e⟩⟩

/-- Choosing actual fiber products does not change the missing input: the Cech form
of the gluing is exactly the abstract amalgamation requirement. -/
theorem cechGluing_iff_amalgamGluing (N : CechNerveData (K := K) S R) :
    CechGluing (K := K) S R N ↔
      ∀ D : F.DescentData (X := cechFamily (K := K) S R)
        (f := cechFamilyHom (K := K) S R),
        Nonempty (Amalgam F (cechFamilyHom (K := K) S R) D) := by
  constructor
  · intro h D
    exact (cechAmalgam_nonempty_iff_amalgam_nonempty_image (K := K) S R N D).mp
      (h ((descentToCech (K := K) S R N).obj D))
  · intro h D
    exact (cechAmalgam_nonempty_iff_amalgam_nonempty (K := K) S R N D).mpr
      (h ((cechToDescent (K := K) S R N).obj D))

/-- The exact first missing of the gluing, in Cech form.  It is exactly effective
descent for the presieve R. -/
theorem cechGluing_iff_effectiveDescent (N : CechNerveData (K := K) S R) :
    CechGluing (K := K) S R N ↔ HasEffectiveDescentPresieve F R := by
  rw [cechGluing_iff_amalgamGluing]
  exact (hasEffectiveDescent_iff_amalgam F
    (fun i : R.category => cechFamilyHom (K := K) S R i)).symm

/-- The Cech gluing requirement is literally S2445's amalgamation requirement for R. -/
theorem S2447CechGluing_iff_S2445AmalgamationRequirement
    (N : CechNerveData (K := K) S R) :
    CechGluing (K := K) S R N ↔ S2445AmalgamationRequirement (K := K) S R := by
  unfold S2445AmalgamationRequirement
  exact cechGluing_iff_amalgamGluing (K := K) S R N

/-- The Cech gluing requirement is not vacuous: if R generates the maximal sieve,
every Cech descent datum has an amalgam. -/
theorem cechGluing_of_generate_top (N : CechNerveData (K := K) S R)
    (hR : Sieve.generate R = ⊤) : CechGluing (K := K) S R N :=
  (cechGluing_iff_effectiveDescent (K := K) S R N).mpr
    (hasEffectiveDescentPresieve_of_generate_top F R hR)

/-- The identity cover has effective descent, hence its actual Cech gluing holds. -/
theorem cechGluing_singleton_id (S : Iut.SchemeOverField K) :
    CechGluing (K := K) S (Presieve.singleton (𝟙 S))
      (cechNerveData (K := K) S (Presieve.singleton (𝟙 S))) :=
  cechGluing_of_generate_top (S := S) (R := Presieve.singleton (𝟙 S))
    (N := cechNerveData (K := K) S (Presieve.singleton (𝟙 S)))
    (hR := Sieve.generate_of_singleton_isSplitEpi (𝟙 S))

/-- Every cover containing a split epimorphism has its actual Cech gluing. -/
theorem cechGluing_of_contains_isSplitEpi (N : CechNerveData (K := K) S R)
    {Y : Iut.SchemeOverField K} (f : Y ⟶ S) [IsSplitEpi f] (hf : R f) :
    CechGluing (K := K) S R N :=
  cechGluing_of_generate_top (S := S) (R := R) (N := N)
    (hR := Sieve.generate_of_contains_isSplitEpi f hf)

end CechDescent

/-! ## 5. The global statement and its identification with the D9 missing input -/

section Global

variable {K : Type} [Field K]

/-- The global actual-Cech gluing statement for the etale topology on schemes over K. -/
def S2447AllCechGluing (K : Type) [Field K] : Prop :=
  ∀ (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S →
      CechGluing (K := K) S R (cechNerveData (K := K) S R)

/-- The global actual-Cech gluing is exactly S2445's global amalgamation requirement.
The construction of the Cech nerve does not weaken or strengthen the named missing
input. -/
theorem S2447AllCechGluing_iff :
    S2447AllCechGluing K ↔ S2445AllCechAmalgamation (K := K) := by
  constructor
  · intro h S R hR
    exact (S2447CechGluing_iff_S2445AmalgamationRequirement (K := K) (S := S) (R := R)
      (cechNerveData (K := K) S R)).mp (h S R hR)
  · intro h S R hR
    exact (S2447CechGluing_iff_S2445AmalgamationRequirement (K := K) (S := S) (R := R)
      (cechNerveData (K := K) S R)).mpr (h S R hR)

/-- Hence the global actual-Cech gluing is exactly S2134's family form of effective
descent, i.e. the effective-descent half of the D9 stack target. -/
theorem S2447AllCechGluing_iff_effectiveDescentFamilies :
    S2447AllCechGluing K ↔ S2134EffDescentOnEtaleFamilies (K := K) :=
  (S2447AllCechGluing_iff (K := K)).trans
    (S2445AllCechAmalgamation_iff (K := K)).symm

end Global



/-! ## 6. Interface and axiom checks -/

#check @chosenPullbackOfHasPullback
#check @chosenPullback₃OfHasPullback
#check @cechFamily
#check @cechFamilyHom
#check @cechSq
#check @cechSq₃
#check @CechNerveData
#check @cechNerveData
#check @CechZero
#check @CechOne
#check @CechTwo
#check @CechOneFst
#check @CechOneSnd
#check @CechOneBase
#check @CechFace₁₂
#check @CechFace₂₃
#check @CechFace₁₃
#check @CechDeg
#check @CechFace₁₂_fst_eq_CechFace₁₃_fst
#check @CechFace₁₂_snd_eq_CechFace₂₃_fst
#check @CechFace₂₃_snd_eq_CechFace₁₃_snd
#check @CechDeg_fst
#check @CechDeg_snd
#check @CechDescentDatum
#check @cechToDescent
#check @descentToCech
#check @cechEquivalence
#check @cechComparison
#check @cechComparison_obj
#check @cechComparison_map
#check @CechAmalgam
#check @CechAmalgam.congr
#check @amalgamToCech
#check @cechToAmalgam
#check @amalgamCongr
#check @cechAmalgam_nonempty_iff_amalgam_nonempty_image
#check @cechAmalgam_nonempty_iff_amalgam_nonempty
#check @CechGluing
#check @CechGluing_iff_essSurj
#check @cechGluing_iff_amalgamGluing
#check @cechGluing_iff_effectiveDescent
#check @S2447CechGluing_iff_S2445AmalgamationRequirement
#check @cechGluing_of_generate_top
#check @cechGluing_singleton_id
#check @cechGluing_of_contains_isSplitEpi
#check @S2447AllCechGluing
#check @S2447AllCechGluing_iff
#check @S2447AllCechGluing_iff_effectiveDescentFamilies

#print axioms CechFace₁₂_fst_eq_CechFace₁₃_fst
#print axioms CechFace₁₂_snd_eq_CechFace₂₃_fst
#print axioms CechFace₂₃_snd_eq_CechFace₁₃_snd
#print axioms CechDeg_fst
#print axioms CechDeg_snd
#print axioms cechComparison_obj
#print axioms cechComparison_map
#print axioms cechAmalgam_nonempty_iff_amalgam_nonempty_image
#print axioms cechAmalgam_nonempty_iff_amalgam_nonempty
#print axioms CechGluing_iff_essSurj
#print axioms cechGluing_iff_amalgamGluing
#print axioms cechGluing_iff_effectiveDescent
#print axioms S2447CechGluing_iff_S2445AmalgamationRequirement
#print axioms cechGluing_of_generate_top
#print axioms cechGluing_singleton_id
#print axioms cechGluing_of_contains_isSplitEpi
#print axioms S2447AllCechGluing_iff
#print axioms S2447AllCechGluing_iff_effectiveDescentFamilies

end LeanFormal.IUT.XiFPaper.S2447CechNerveActual
