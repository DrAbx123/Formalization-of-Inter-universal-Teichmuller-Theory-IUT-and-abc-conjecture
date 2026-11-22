
/-! ## 4. The quotient and (G2) for (FiniteEtale K)^op -/

section Quotients

variable {K : Type u} [Field K]

/-- The category of finite etale K-algebras, opposite to the category of finite etale
affine K-schemes.  This is the Galois category whose objects are finite etale covers of
Spec K. -/
abbrev FiniteEtaleAlg (K : Type u) [Field K] : Type (u + 1) :=
  (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ

namespace FiniteEtaleAlg

instance category : Category.{u, u + 1} (FiniteEtaleAlg K) := inferInstance

/-- Lenstra (G2), field hasQuotientsByFiniteGroups.  For every finite group G,
the category (FiniteEtale K)^op has colimits of shape SingleObj G.

The colimit of a G-action on a finite etale algebra A is its invariant subalgebra
A^G, with quotient map A -> A^G in (FiniteEtale K)^op (the opposite of the
inclusion A^G -> A). -/
instance hasQuotientsByFiniteGroups (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K) :=
  hasColimitsOfShape_op_of_hasLimitsOfShape (J := SingleObj G)
    (C := CommAlgCat.FiniteEtale.{u} K)

end FiniteEtaleAlg

end Quotients

/-! ## 5. Filling the hasQuotientsByFiniteGroups field

PreGaloisCategory has five axioms.  This file proves the fourth one
(hasQuotientsByFiniteGroups) unconditionally; the assembly below shows that it can be
plugged into the structure, leaving the other fields as hypotheses. -/

section Assembly

variable {K : Type u} [Field K]

/-- The exact statement of the fourth field of PreGaloisCategory (FiniteEtaleAlg K). -/
abbrev HasQuotientsByFiniteGroupsField : Prop :=
  forall (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleAlg K)

/-- The field is now unconditional. -/
theorem hasQuotientsByFiniteGroupsField_holds :
    HasQuotientsByFiniteGroupsField (K := K) :=
  fun _ _ _ => inferInstance

/-- Assembling a PreGaloisCategory (FiniteEtaleAlg K) from the other four fields: the
fourth field (hasQuotientsByFiniteGroups) is supplied by the invariant subalgebra. -/
theorem preGaloisCategoryOfOtherFields
    (hTerm : HasTerminal (FiniteEtaleAlg K))
    (hPull : HasPullbacks (FiniteEtaleAlg K))
    (hCoprod : HasFiniteCoproducts (FiniteEtaleAlg K))
    (hMono : forall {X Y : FiniteEtaleAlg K} (i : X ⟶ Y), Mono i →
      ∃ (Z : FiniteEtaleAlg K) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))) :
    PreGaloisCategory (FiniteEtaleAlg K) where
  hasTerminal := hTerm
  hasPullbacks := hPull
  hasFiniteCoproducts := hCoprod
  hasQuotientsByFiniteGroups := fun _ _ _ => inferInstance
  monoInducesIsoOnDirectSummand := hMono

end Assembly

/-! ## 6. Axiom audit -/

#print axioms S1770.finiteSplit_of_injective_pi
#print axioms S1770.etale_subalgebra
#print axioms S1770.fixedSubalgebra
#print axioms S1770.invariants
#print axioms S1770.invariantsFinite
#print axioms S1770.invariantsEtale
#print axioms S1770.invariantsCone
#print axioms S1770.invariantsLift
#print axioms S1770.existsUnique_lift_fixedSubalgebra
#print axioms S1770.quotientMap
#print axioms S1770.invariantsLift_fac
#print axioms S1770.invariantsIsLimit
#print axioms S1770.hasLimitInvariants
#print axioms S1770.hasLimitsOfShapeOpSingleObj
#print axioms S1770.FiniteEtaleAlg.hasQuotientsByFiniteGroups
#print axioms S1770.hasQuotientsByFiniteGroupsField_holds
#print axioms S1770.preGaloisCategoryOfOtherFields

end S1770