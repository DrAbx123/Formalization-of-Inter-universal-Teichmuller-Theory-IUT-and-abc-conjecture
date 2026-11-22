import Iut.Foundations.Orbicurve
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# S2 axiom probe and L1-F2 consumer evidence

No production file is modified.

Part A repeats verbatim the central S2 transport proof from
tmp/sheaf/l03-g2/S2Transport.lean (the serialized wrapper does not support -o,
so S2Transport.olean is unavailable) and prints its axioms. The local theorem
has the same statement and proof body as S2Transport.

Part B records the L1-F2 consumer reduction: once kummer's scheme HasColimits
theorem is available, the curve scheme G2 target and the remaining-fields
structure follow by exact/constructor.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.S2Axioms

universe u

open Iut
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {S : SchemeOverField F}

/-- Verbatim copy of the S2 transport statement/proof for axiom probing. -/
theorem s2_hasColimitsOfShape_orbicurve_of_equivalence
    [Category.{u} (OrbicurveFiniteEtaleCover X)]
    (E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X)
    [E.IsEquivalence]
    (hS : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left)) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X) := by
  intro G _ _
  letI : HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left) :=
    hS G
  exact Adjunction.hasColimitsOfShape_of_equivalence (E := E.inv)

/-- Verbatim copy of the direct-hypothesis wrapper. -/
theorem s2_hasColimitsOfShape_orbicurve_of_scheme
    [Category.{u} (OrbicurveFiniteEtaleCover X)]
    (E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X)
    [E.IsEquivalence]
    (hS : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left)) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X) :=
  s2_hasColimitsOfShape_orbicurve_of_equivalence (X := X) (S := S) E hS

#print axioms s2_hasColimitsOfShape_orbicurve_of_equivalence
#print axioms s2_hasColimitsOfShape_orbicurve_of_scheme

/-! ## Part B: L1-F2 consumer evidence -/

/-- If kummer's scheme-level finite-group colimit theorem is available for
curveScheme K, then the L1-F2 target follows by exacting it. -/
theorem l1f2_curveScheme_hasQuotientsByFiniteGroups_of_kummer
    (K : Type u) [Field K]
    (kummer :
      ∀ (G : Type u) [Group G] [Finite G],
        HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K)) :=
  kummer

/-- The same kummer theorem enters the frozen L1-F2 remaining-fields structure. -/
noncomputable def l1f2_curveScheme_remainingFields_of_kummer
    (K : Type u) [Field K]
    (kummer :
      ∀ (G : Type u) [Group G] [Finite G],
        HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))) :
    CurvePreGaloisCategoryRemainingFields (curveScheme K) where
  hasQuotientsByFiniteGroups := kummer

/-- Consumer evidence package: target theorem and remaining-fields entry are
both direct from kummer's theorem. -/
theorem l1f2_consumer_reduction
    (K : Type u) [Field K]
    (kummer :
      ∀ (G : Type u) [Group G] [Finite G],
        HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))) :
    (∀ (G : Type u) [Group G] [Finite G],
        HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K))) ∧
      Nonempty (CurvePreGaloisCategoryRemainingFields (curveScheme K)) :=
  ⟨l1f2_curveScheme_hasQuotientsByFiniteGroups_of_kummer K kummer,
    ⟨l1f2_curveScheme_remainingFields_of_kummer K kummer⟩⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.S2Axioms
