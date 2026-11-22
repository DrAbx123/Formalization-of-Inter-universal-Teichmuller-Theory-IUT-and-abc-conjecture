import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Ring.Aut
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

noncomputable section

namespace ABCBridge.CoverSectionsAction

universe u

variable {R : Type u} [CommRing R]
variable (X : FiniteEtaleCover (Spec (CommRingCat.of R)))
variable {G : Type u} [Group G]

/-- The section ring of a finite etale cover over an affine base. -/
abbrev CoverSections : Type u := Γ(X.carrier, ⊤)

/-- The production Algebra R structure on the sections. -/
noncomputable abbrev coverSectionsAlgebra : Algebra R (CoverSections X) :=
  finiteEtaleCoverSectionsAlgebra R X

/-- A scheme automorphism of the carrier, obtained from an automorphism of the
cover by forgetting the structure map. -/
noncomputable def coverAutSchemeIso (act : G →* CategoryTheory.Aut X) (g : G) :
    X.carrier ≅ X.carrier :=
  (FiniteEtaleCover.forget (Spec (CommRingCat.of R))).mapIso (act g)

/-- The induced ring automorphism of the section ring. -/
noncomputable def coverSectionsRingEquiv (act : G →* CategoryTheory.Aut X) (g : G) :
    CoverSections X ≃+* CoverSections X :=
  (Scheme.Γ.mapIso (coverAutSchemeIso X act g).op).commRingCatIsoToRingEquiv




/-- Composition order for the ring equivalence associated with a commutative-ring
isomorphism: composition corresponds to the product in the automorphism group. -/
theorem commRingCatIsoToRingEquiv_trans_anti {A : CommRingCat.{u}}
    (e f : A ≅ A) :
    (e ≪≫ f).commRingCatIsoToRingEquiv =
      f.commRingCatIsoToRingEquiv * e.commRingCatIsoToRingEquiv := by
  ext a
  change (f.hom.hom (e.hom.hom a)) =
    f.commRingCatIsoToRingEquiv (e.commRingCatIsoToRingEquiv a)
  rfl

/-- The section-ring automorphism of the identity cover automorphism is the
identity. -/
theorem coverSectionsRingEquiv_one (act : G →* CategoryTheory.Aut X) :
    coverSectionsRingEquiv X act 1 = 1 := by
  unfold coverSectionsRingEquiv coverAutSchemeIso
  rw [map_one act]
  have hone : (1 : CategoryTheory.Aut X) = Iso.refl X := rfl
  simp only [hone]
  ext a
  rfl

/-- The section-ring automorphism is an anti-homomorphism. -/
theorem coverSectionsRingEquiv_anti (act : G →* CategoryTheory.Aut X) (g h : G) :
    coverSectionsRingEquiv X act (g * h) =
      coverSectionsRingEquiv X act h * coverSectionsRingEquiv X act g := by
  unfold coverSectionsRingEquiv coverAutSchemeIso
  rw [map_mul act, CategoryTheory.Aut.Aut_mul_def, Functor.mapIso_trans]
  erw [Iso.op_trans, Functor.mapIso_trans]
  exact commRingCatIsoToRingEquiv_trans_anti _ _

/-- The induced monoid homomorphism on section-ring automorphisms, using the
inverse automorphism to turn the anti-homomorphism into a left action. -/
noncomputable def coverSectionsActionHom (act : G →* CategoryTheory.Aut X) :
    G →* (CoverSections X ≃+* CoverSections X) where
  toFun g := coverSectionsRingEquiv X act g⁻¹
  map_one' := by
    simpa using coverSectionsRingEquiv_one X act
  map_mul' g h := by
    rw [mul_inv_rev, coverSectionsRingEquiv_anti]

/-- The induced multiplicative semiring action on the section ring. -/
@[reducible] noncomputable def coverSectionsMulSemiringAction
    (act : G →* CategoryTheory.Aut X) : MulSemiringAction G (CoverSections X) :=
  letI : MulSemiringAction (CoverSections X ≃+* CoverSections X) (CoverSections X) :=
    inferInstance
  MulSemiringAction.compHom (M := CoverSections X ≃+* CoverSections X)
    (R := CoverSections X) (coverSectionsActionHom X act)



/-- The cover automorphism commutes with the structure morphism. -/
theorem coverAutSchemeIso_structureMap
    (act : G →* CategoryTheory.Aut X) (g : G) :
    (coverAutSchemeIso X act g).hom ≫ X.structureMap = X.structureMap := by
  have h := ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).mapIso (act g)).hom.w
  exact h

/-- The induced section-ring automorphism fixes the structure constants. -/
theorem coverSectionsRingEquiv_algebraMap
    (act : G →* CategoryTheory.Aut X) (g : G) (r : R) :
    coverSectionsRingEquiv X act g (algebraMap R (CoverSections X) r) =
      algebraMap R (CoverSections X) r := by
  letI := finiteEtaleCoverSectionsAlgebra R X
  change coverSectionsRingEquiv X act g
      (finiteEtaleCoverSectionsAlgebraMap R X r) = finiteEtaleCoverSectionsAlgebraMap R X r
  have h := congrArg Scheme.Hom.appTop (coverAutSchemeIso_structureMap X act g)
  rw [Scheme.Hom.comp_appTop] at h
  have h' := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h
  change (Scheme.Hom.appTop (coverAutSchemeIso X act g).hom)
      ((Scheme.Hom.appTop X.structureMap) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
    (Scheme.Hom.appTop X.structureMap) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  exact h'

/-- The induced action on sections is R-linear. -/
theorem coverSectionsSMulCommClass (act : G →* CategoryTheory.Aut X) :
    letI := coverSectionsMulSemiringAction X act
    SMulCommClass G R (CoverSections X) := by
  letI := coverSectionsMulSemiringAction X act
  exact
    { smul_comm := fun g r a => by
        change coverSectionsRingEquiv X act g⁻¹
            (algebraMap R (CoverSections X) r * a) =
          algebraMap R (CoverSections X) r *
            coverSectionsRingEquiv X act g⁻¹ a
        rw [map_mul, coverSectionsRingEquiv_algebraMap] }

/-- The fixed-point subalgebra of the induced action on sections. -/
noncomputable def coverSectionsFixedPoints (act : G →* CategoryTheory.Aut X) :
    Subalgebra R (CoverSections X) :=
  letI := coverSectionsMulSemiringAction X act
  letI := coverSectionsSMulCommClass X act
  FixedPoints.subalgebra R (CoverSections X) G


/-- The set of sections fixed by every induced ring automorphism. -/
def coverSectionsInvariantSet (act : G →* CategoryTheory.Aut X) :
    Set (CoverSections X) :=
  {a | ∀ g : G, coverSectionsRingEquiv X act g a = a}

/-- Membership in the invariant section set is exactly invariance. -/
theorem mem_coverSectionsInvariantSet_iff
    (act : G →* CategoryTheory.Aut X) (a : CoverSections X) :
    a ∈ coverSectionsInvariantSet X act ↔
      ∀ g : G, coverSectionsRingEquiv X act g a = a :=
  Iff.rfl

/-- A section fixed by all induced automorphisms is fixed by the identity. -/
theorem coverSectionsInvariantSet_one
    (act : G →* CategoryTheory.Aut X) (a : CoverSections X) :
    a ∈ coverSectionsInvariantSet X act →
      coverSectionsRingEquiv X act 1 a = a :=
  fun h => h 1

/-- Invariant sections are closed under multiplication. -/
theorem coverSectionsInvariantSet_mul
    (act : G →* CategoryTheory.Aut X) {a b : CoverSections X}
    (ha : a ∈ coverSectionsInvariantSet X act)
    (hb : b ∈ coverSectionsInvariantSet X act) :
    a * b ∈ coverSectionsInvariantSet X act := by
  intro g
  rw [map_mul, ha g, hb g]

/-- Invariant sections are closed under addition. -/
theorem coverSectionsInvariantSet_add
    (act : G →* CategoryTheory.Aut X) {a b : CoverSections X}
    (ha : a ∈ coverSectionsInvariantSet X act)
    (hb : b ∈ coverSectionsInvariantSet X act) :
    a + b ∈ coverSectionsInvariantSet X act := by
  intro g
  rw [map_add, ha g, hb g]

/-- Zero is an invariant section. -/
theorem coverSectionsInvariantSet_zero
    (act : G →* CategoryTheory.Aut X) :
    (0 : CoverSections X) ∈ coverSectionsInvariantSet X act := by
  intro g
  simp

/-- One is an invariant section. -/
theorem coverSectionsInvariantSet_one_mem
    (act : G →* CategoryTheory.Aut X) :
    (1 : CoverSections X) ∈ coverSectionsInvariantSet X act := by
  intro g
  simp

/-- The Spec automorphism induced by the section-ring automorphism. -/
noncomputable def coverSectionsSpecAut (act : G →* CategoryTheory.Aut X) (g : G) :
    Spec (CommRingCat.of (CoverSections X)) ≅
      Spec (CommRingCat.of (CoverSections X)) :=
  Scheme.Spec.mapIso ((coverSectionsRingEquiv X act g).toCommRingCatIso.op)

/-- The canonical affine isomorphism of the carrier with the Spectrum of its
section ring. -/
noncomputable def coverSectionsIsoSpec [IsAffine X.carrier] :
    X.carrier ≅ Spec (CommRingCat.of (CoverSections X)) :=
  X.carrier.isoSpec

/-- The induced Spec automorphism agrees with the cover automorphism under the
canonical affine isomorphism. -/
theorem coverSectionsSpecAut_agrees
    [IsAffine X.carrier]
    (act : G →* CategoryTheory.Aut X) (g : G) :
    (coverSectionsIsoSpec X).hom ≫ (coverSectionsSpecAut X act g).hom =
      (coverAutSchemeIso X act g).hom ≫ (coverSectionsIsoSpec X).hom := by
  unfold coverSectionsIsoSpec coverSectionsSpecAut coverAutSchemeIso
    coverSectionsRingEquiv
  change X.carrier.isoSpec.hom ≫
      Spec.map ((coverAutSchemeIso X act g).hom.appTop) =
    (coverAutSchemeIso X act g).hom ≫ X.carrier.isoSpec.hom
  rw [Scheme.isoSpec_hom_naturality]


/-- Invariant sections are closed under negation. -/
theorem coverSectionsInvariantSet_neg
    (act : G →* CategoryTheory.Aut X) {a : CoverSections X}
    (ha : a ∈ coverSectionsInvariantSet X act) :
    -a ∈ coverSectionsInvariantSet X act := by
  intro g
  rw [map_neg, ha g]

/-- Invariant sections are closed under subtraction. -/
theorem coverSectionsInvariantSet_sub
    (act : G →* CategoryTheory.Aut X) {a b : CoverSections X}
    (ha : a ∈ coverSectionsInvariantSet X act)
    (hb : b ∈ coverSectionsInvariantSet X act) :
    a - b ∈ coverSectionsInvariantSet X act := by
  intro g
  rw [map_sub, ha g, hb g]

/-- Invariant sections are closed under powers. -/
theorem coverSectionsInvariantSet_pow
    (act : G →* CategoryTheory.Aut X) {a : CoverSections X}
    (ha : a ∈ coverSectionsInvariantSet X act) (n : ℕ) :
    a ^ n ∈ coverSectionsInvariantSet X act := by
  intro g
  rw [map_pow, ha g]

/-- Natural-number constants are invariant sections. -/
theorem coverSectionsInvariantSet_natCast
    (act : G →* CategoryTheory.Aut X) (n : ℕ) :
    (n : CoverSections X) ∈ coverSectionsInvariantSet X act := by
  intro g
  simp

/-- Integer constants are invariant sections. -/
theorem coverSectionsInvariantSet_intCast
    (act : G →* CategoryTheory.Aut X) (n : ℤ) :
    (n : CoverSections X) ∈ coverSectionsInvariantSet X act := by
  intro g
  simp

/-- The invariant sections form a subring of the section ring. -/
noncomputable def coverSectionsInvariantSubring
    (act : G →* CategoryTheory.Aut X) : Subring (CoverSections X) where
  carrier := coverSectionsInvariantSet X act
  zero_mem' := coverSectionsInvariantSet_zero X act
  one_mem' := coverSectionsInvariantSet_one_mem X act
  add_mem' := coverSectionsInvariantSet_add X act
  mul_mem' := coverSectionsInvariantSet_mul X act
  neg_mem' := coverSectionsInvariantSet_neg X act

/-- Membership in the invariant subring is invariance. -/
theorem mem_coverSectionsInvariantSubring_iff
    (act : G →* CategoryTheory.Aut X) (a : CoverSections X) :
    a ∈ coverSectionsInvariantSubring X act ↔
      ∀ g : G, coverSectionsRingEquiv X act g a = a :=
  Iff.rfl

/-- The underlying set of the invariant subring is the invariant section set. -/
theorem coverSectionsInvariantSubring_carrier
    (act : G →* CategoryTheory.Aut X) :
    (coverSectionsInvariantSubring X act : Set (CoverSections X)) =
      coverSectionsInvariantSet X act :=
  rfl


/-- The induced action is the inverse section-ring automorphism. -/
theorem coverSections_smul_def (act : G →* CategoryTheory.Aut X) (g : G)
    (a : CoverSections X) :
    letI := coverSectionsMulSemiringAction X act
    g • a = coverSectionsRingEquiv X act g⁻¹ a :=
  rfl

/-- The fixed-point subalgebra of the action is exactly the invariant section
set. -/
theorem coverSectionsFixedPoints_eq_invariantSet
    (act : G →* CategoryTheory.Aut X) :
    (coverSectionsFixedPoints X act : Set (CoverSections X)) =
      coverSectionsInvariantSet X act := by
  ext a
  letI := coverSectionsMulSemiringAction X act
  letI := coverSectionsSMulCommClass X act
  change (a ∈ FixedPoints.subalgebra R (CoverSections X) G) ↔
    a ∈ coverSectionsInvariantSet X act
  simp [FixedPoints.subalgebra, coverSectionsInvariantSet, coverSections_smul_def]
  constructor
  · intro h g
    have hg := h g⁻¹
    rw [coverSections_smul_def] at hg
    simpa using hg
  · intro h g
    rw [coverSections_smul_def]
    exact h g⁻¹

end ABCBridge.CoverSectionsAction
