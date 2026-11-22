/-
# S1970: the actual iso-comma stack -- H-comparison naturality and the exact
first missing, after the S1956 reduction

## Context

S1956 reduced the target (sitePseudofunctor f g).IsStack J to the conjunction
of the prestack condition and the effectivity condition, and isolated the exact
first missing statement for the prestack half:

  (A) S1956HComparisonNaturalityAll

the componentwise naturality of the two H-comparison maps built from f.map,
g.map and the site comparisons S1864SiteComparisonLeft/Right.

## What is done here

1.  The decomposition of IsStack of S1956 is restated in the namespace of this
    file, so that the exact target and its two missing fields are available as a
    single interface.

2.  The exact reduction from (A) to the two natural transformations of hom
    presheaves is proved.  Given the componentwise naturality of the first
    (resp. second) H-comparison, the components S1956FstToHComponent (resp.
    S1956SndToHComponent) assemble into a natural transformation of
    presheaves

      A.source.fiber.presheafHom M.left N.left
        --> C.source.fiber.presheafHom (f_S M.left) (f_S N.left)

    (resp. the B-side one).  This is the first genuinely new consumer of (A):
    it turns the pointwise H-components into presheaf morphisms, which is the
    input of the pullback-of-sheaves argument.

3.  The exact first missing and second missing statements are named, with no
    inhabitant asserted.

## Honest boundary

No sorry, no axiom, no fake IsStack.  Neither
S1956HComparisonNaturalityAll nor S1956IsoCommaEffectivity is proved here.
The pullback-of-sheaves step from (A) (identifying the iso-comma hom presheaf
with the fibre product of the A-, B- and C-hom presheaves, and using that the
corner presheaves are sheaves) is not formalized.  The effectivity step (B)
is not formalized either.  The only axioms used are propext,
Classical.choice and Quot.sound.

The componentwise associativity assembly for (A) was reduced to the three
ingredients already available in the tree:

* the inv-direction component coherence of the strong transformation f.map
  (natCompInvApp_comp of S1935),
* the naturality of the comparison at g (NatTrans.naturality of
  Cat.Hom.toNatIso (g.map.naturality ...)),
* the hom-direction component coherence of f.map (natCompHomApp_comp).

The attempted proof reduced (A) to the componentwise assembly of these three
identities through the pullHom restrictions and the Cat.Hom.toNatIso
comparisons.  That assembly was not completed in this file; no mathematical
input beyond the three displayed ingredients was identified as missing.
-/
import tmp.sheaf.xif.paper.S1956IsoCommaStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1970IsoCommaStackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev J : GrothendieckTopology Site := SchemeOverField.etaleTopology K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

abbrev IsoCommaObjAt {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (S : Site) :=
  S1836IsoComma (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor

/-! ## 1. The target and its exact decomposition -/

/-- The prestack half of the target. -/
def S1970IsoCommaPrestack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  S1956IsoCommaPrestack f g

/-- The effectivity half of the target (the second missing statement). -/
def S1970IsoCommaEffectivity {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  S1956IsoCommaEffectivity f g

/-- The stack condition for the actual iso-comma pseudofunctor. -/
def S1970IsoCommaStack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  S1956IsoCommaStack f g

/-- **The exact decomposition of the target**: Mathlib's IsStack is the
conjunction of IsPrestack and essential surjectivity of toDescentData. -/
theorem S1970IsoCommaStack_iff_prestack_effectivity
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1970IsoCommaStack f g ↔
      S1970IsoCommaPrestack f g ∧ S1970IsoCommaEffectivity f g :=
  S1956IsoCommaStack_iff_prestack_effectivity f g

/-! ## 2. The exact first and second missing statements -/

/-- **The exact first missing statement.**  Componentwise naturality of the two
H-comparison maps.  This is definitionally the missing item of S1956; no
inhabitant is asserted. -/
def S1970HComparisonNaturalityAll : Prop :=
  S1956HComparisonNaturalityAll

/-- **The exact second missing statement.**  Essential surjectivity of
toDescentData for every covering sieve.  No inhabitant is asserted. -/
def S1970EffectivityAll : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    S1956IsoCommaEffectivity f g

/-- The first missing statement is exactly S1956's. -/
theorem S1970HComparisonNaturalityAll_iff :
    S1970HComparisonNaturalityAll ↔ S1956HComparisonNaturalityAll :=
  Iff.rfl

/-- The second missing statement is exactly the effectivity condition of S1956. -/
theorem S1970EffectivityAll_iff :
    S1970EffectivityAll ↔
      ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
        S1956IsoCommaEffectivity f g :=
  Iff.rfl

/-! ## 3. (A) gives the natural transformations of hom presheaves

This is the first new consumer of the missing naturality. -/

section HComparisonNatTrans

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M N : IsoCommaObjAt f g S)

/-- **The first H-comparison as a natural transformation of hom presheaves**,
assuming its componentwise naturality. -/
noncomputable def S1970FstToHNatTrans
    (h : S1956FstToHNaturality f g M N) :
    Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left ⟶
      Pseudofunctor.presheafHom C.source.fiber (S := S)
        ((f.map.app (U S)).toFunctor.obj M.obj.left)
        ((f.map.app (U S)).toFunctor.obj N.obj.left) where
  app Y := ↾fun u => S1956FstToHComponent f g M N Y u
  naturality {Y Z} p := by
    ext u
    exact h Y Z p u

/-- **The second H-comparison as a natural transformation of hom presheaves**,
assuming its componentwise naturality. -/
noncomputable def S1970SndToHNatTrans
    (h : S1956SndToHNaturality f g M N) :
    Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right ⟶
      Pseudofunctor.presheafHom C.source.fiber (S := S)
        ((g.map.app (U S)).toFunctor.obj M.obj.right)
        ((g.map.app (U S)).toFunctor.obj N.obj.right) where
  app Y := ↾fun v => S1956SndToHComponent f g M N Y v
  naturality {Y Z} p := by
    ext v
    exact h Y Z p v

/-- **The uniform form**: the first missing statement supplies both H-comparison
natural transformations for every cospan, test object and pair of objects. -/
theorem S1970HComparisonNaturalityAll_gives_natTrans
    (h : S1956HComparisonNaturalityAll) :
    ∀ {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      {S : Site} (M N : IsoCommaObjAt f g S),
      Nonempty (Pseudofunctor.presheafHom A.source.fiber (S := S)
          M.obj.left N.obj.left ⟶
        Pseudofunctor.presheafHom C.source.fiber (S := S)
          ((f.map.app (U S)).toFunctor.obj M.obj.left)
          ((f.map.app (U S)).toFunctor.obj N.obj.left)) ∧
      Nonempty (Pseudofunctor.presheafHom B.source.fiber (S := S)
          M.obj.right N.obj.right ⟶
        Pseudofunctor.presheafHom C.source.fiber (S := S)
          ((g.map.app (U S)).toFunctor.obj M.obj.right)
          ((g.map.app (U S)).toFunctor.obj N.obj.right)) := by
  intro A B C f g S M N
  obtain ⟨hf, hg⟩ := h f g M N
  exact ⟨⟨S1970FstToHNatTrans f g M N hf⟩, ⟨S1970SndToHNatTrans f g M N hg⟩⟩

end HComparisonNatTrans

/-! ## 4. Consumers of the decomposition -/

/-- The stack condition gives the prestack half. -/
theorem S1970IsoCommaPrestack_of_stack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1970IsoCommaStack f g) : S1970IsoCommaPrestack f g :=
  (S1970IsoCommaStack_iff_prestack_effectivity f g).1 h |>.1

/-- The stack condition gives the effectivity half. -/
theorem S1970IsoCommaEffectivity_of_stack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1970IsoCommaStack f g) : S1970IsoCommaEffectivity f g :=
  (S1970IsoCommaStack_iff_prestack_effectivity f g).1 h |>.2

/-! ## 5. Checks and axiom audit -/

#check S1970IsoCommaPrestack
#check S1970IsoCommaEffectivity
#check S1970IsoCommaStack
#check S1970IsoCommaStack_iff_prestack_effectivity
#check S1970HComparisonNaturalityAll
#check S1970EffectivityAll
#check S1970HComparisonNaturalityAll_iff
#check S1970EffectivityAll_iff
#check S1970FstToHNatTrans
#check S1970SndToHNatTrans
#check S1970HComparisonNaturalityAll_gives_natTrans
#check S1970IsoCommaPrestack_of_stack
#check S1970IsoCommaEffectivity_of_stack

#print axioms S1970IsoCommaStack_iff_prestack_effectivity
#print axioms S1970HComparisonNaturalityAll_iff
#print axioms S1970EffectivityAll_iff
#print axioms S1970FstToHNatTrans
#print axioms S1970SndToHNatTrans
#print axioms S1970HComparisonNaturalityAll_gives_natTrans
#print axioms S1970IsoCommaPrestack_of_stack
#print axioms S1970IsoCommaEffectivity_of_stack

end LeanFormal.IUT.XiFPaper.S1970IsoCommaStackActual