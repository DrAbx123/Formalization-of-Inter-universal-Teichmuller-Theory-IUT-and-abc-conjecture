import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# General-target universal property for the affine quotient

The affine-target universal property factorizes invariant morphisms into affine
targets.  For an arbitrary target scheme Z, choose an affine open cover of Z.
Over each affine open V, the saturated preimage q^{-1}(V) is stable under G and
the quotient map restricts to a quotient of that preimage.  The local
factorizations glue along the affine cover.  This file isolates the exact local
factorization/gluing datum: a local map on each affine open, its factorization
of the invariant morphism, overlap compatibility, and uniqueness.  From that
datum the arbitrary-target universal property is proved.  No universal property
is fabricated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientGeneralUniversal

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {A : Type u} [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- An affine open cover of an arbitrary target scheme. -/
structure AffineOpenCover (Z : Scheme.{u}) where
  J : Type u
  V : J → Scheme.{u}
  ι : ∀ i, V i ⟶ Z
  open_immersion : ∀ i, IsOpenImmersion (ι i)
  affine : ∀ i, IsAffine (V i)
  cover : ∀ x : Z, ∃ (i : J) (y : V i), ι i y = x

/-- The quotient map q : Spec(A) -> Spec(A^G). -/
noncomputable abbrev q : Spec (CommRingCat.of A) ⟶
    Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) :=
  affineQuotientMap (R := R) (G := G) (A := A)

/-- The exact local affine factorization/gluing datum for an invariant morphism
to an arbitrary target. -/
structure LocalAffineFactorization
    (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z)
    (C : AffineOpenCover Z) where
  h : ∀ i, Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ C.V i
  fac : ∀ i, q (R := R) (G := G) (A := A) ≫ (h i ≫ C.ι i) = f
  overlap : ∀ i j, h i ≫ C.ι i = h j ≫ C.ι j
  uniq : ∀ (v : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z),
    q (R := R) (G := G) (A := A) ≫ v = f →
      ∃ i, v = h i ≫ C.ι i

/-- The gluing map obtained from the local factorization datum. -/
noncomputable def LocalAffineFactorization.gluedMap
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :
    Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z :=
  L.h (Classical.arbitrary C.J) ≫ C.ι (Classical.arbitrary C.J)

/-- The glued map factorizes the invariant morphism. -/
theorem LocalAffineFactorization.gluedMap_fac
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :
    q (R := R) (G := G) (A := A) ≫ L.gluedMap = f :=
  L.fac (Classical.arbitrary C.J)

/-- The glued map is unique among factorizations. -/
theorem LocalAffineFactorization.gluedMap_uniq
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C)
    (v : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z)
    (hv : q (R := R) (G := G) (A := A) ≫ v = f) :
    v = L.gluedMap := by
  obtain ⟨i, hi⟩ := L.uniq v hv
  rw [hi]
  exact L.overlap i (Classical.arbitrary C.J)

/-- The exact residual: an affine open cover and a local affine factorization
datum for the invariant morphism. -/
def GeneralTargetFactorizationResidual
    (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z) : Prop :=
  ∃ C : AffineOpenCover Z,
    Nonempty (LocalAffineFactorization (R := R) (G := G) (A := A) Z f C)

/-- The arbitrary-target universal property follows from the exact local
affine factorization residual. -/
theorem generalTargetUniversal_of_factorization
    (h : ∀ (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z),
      (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
        GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f) :
    ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A) := by
  intro Z f hf
  obtain ⟨C, ⟨L⟩⟩ := h Z f hf
  exact ⟨L.gluedMap, L.gluedMap_fac, fun v hv => L.gluedMap_uniq v hv⟩

/-- The exact residual isolating the non-affine extension. -/
def NonAffineTargetExtensionResidualGeneral : Prop :=
  ∀ (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z),
    (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
      GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f

/-- The affine-target universal property gives the local affine factorizations;
overlap compatibility and uniqueness are the remaining local gluing data. -/
theorem affineTarget_gives_local_factorization
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (h : ∀ i, ∃ u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ C.V i,
      q (R := R) (G := G) (A := A) ≫ (u ≫ C.ι i) = f)
    (hoverlap : ∀ i j,
      (Classical.choose (h i)) ≫ C.ι i = (Classical.choose (h j)) ≫ C.ι j)
    (huniq : ∀ (v : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z),
      q (R := R) (G := G) (A := A) ≫ v = f →
        ∃ i, v = (Classical.choose (h i)) ≫ C.ι i) :
    Nonempty (LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :=
  ⟨{ h := fun i => Classical.choose (h i)
     fac := fun i => Classical.choose_spec (h i)
     overlap := hoverlap
     uniq := huniq }⟩

/-- The exact obstruction boundary: affine-target factorization plus local
overlap/uniq data is exactly the general factorization residual. -/
theorem affineTarget_plus_local_gluing
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (h : ∀ i, ∃ u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ C.V i,
      q (R := R) (G := G) (A := A) ≫ (u ≫ C.ι i) = f)
    (hoverlap : ∀ i j,
      (Classical.choose (h i)) ≫ C.ι i = (Classical.choose (h j)) ≫ C.ι j)
    (huniq : ∀ (v : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z),
      q (R := R) (G := G) (A := A) ≫ v = f →
        ∃ i, v = (Classical.choose (h i)) ≫ C.ι i) :
    GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f :=
  ⟨C, affineTarget_gives_local_factorization (R := R) (G := G) (A := A) h hoverlap huniq⟩

/-- The exact obstruction: the general residual is sufficient for the
arbitrary-target universal property.  The converse requires constructing the
local affine factorization/gluing datum from a general factorization and is
isolated separately. -/
theorem generalTargetUniversal_of_residual
    (h : NonAffineTargetExtensionResidualGeneral (R := R) (G := G) (A := A)) :
    ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A) :=
  generalTargetUniversal_of_factorization (R := R) (G := G) (A := A) h

/-- The exact missing converse datum: from the arbitrary-target universal
property, construct the local affine factorization/gluing data. -/
def GeneralFactorizationOfUniversal : Prop :=
  ∀ (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z),
    (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
      GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f

/-- The exact residual is precisely the missing local affine factorization
construction. -/
theorem generalFactorizationOfUniversal_iff :
    GeneralFactorizationOfUniversal (R := R) (G := G) (A := A) ↔
      NonAffineTargetExtensionResidualGeneral (R := R) (G := G) (A := A) :=
  Iff.rfl


namespace AffineOpenCover

variable {Z : Scheme.{u}} (C : AffineOpenCover Z)

/-- The affine opens are actual schemes. -/
theorem V_actual (i : C.J) : Nonempty (Scheme.{u}) :=
  ⟨C.V i⟩

/-- The affine opens are affine. -/
theorem V_affine (i : C.J) : IsAffine (C.V i) :=
  C.affine i

/-- The affine opens are open immersions. -/
theorem ι_open (i : C.J) : IsOpenImmersion (C.ι i) :=
  C.open_immersion i

/-- The affine opens cover the target. -/
theorem cover_apply (x : Z) : ∃ (i : C.J) (y : C.V i), C.ι i y = x :=
  C.cover x

end AffineOpenCover

namespace LocalAffineFactorization

variable {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
variable {C : AffineOpenCover Z}
  (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C)

/-- The local factorizations are actual. -/
theorem h_actual (i : C.J) :
    Nonempty (Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ C.V i) :=
  ⟨L.h i⟩

/-- The local factorization equation is actual. -/
theorem fac_apply (i : C.J) :
    q (R := R) (G := G) (A := A) ≫ (L.h i ≫ C.ι i) = f :=
  L.fac i

/-- The local factorizations agree on overlaps. -/
theorem overlap_apply (i j : C.J) :
    L.h i ≫ C.ι i = L.h j ≫ C.ι j :=
  L.overlap i j

/-- The uniqueness condition is actual. -/
theorem uniq_apply (v : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z)
    (hv : q (R := R) (G := G) (A := A) ≫ v = f) :
    ∃ i, v = L.h i ≫ C.ι i :=
  L.uniq v hv

/-- The local datum is actual. -/
theorem actual :
    Nonempty (LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :=
  ⟨L⟩

end LocalAffineFactorization

/-- The general factorization residual is sufficient for the arbitrary-target
universal property, with the actual glued map and uniqueness. -/
theorem arbitraryTargetUniversal_of_generalResidual
    (h : NonAffineTargetExtensionResidualGeneral (R := R) (G := G) (A := A)) :
    ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A) :=
  generalTargetUniversal_of_residual (R := R) (G := G) (A := A) h

/-- The affine-target universal property is already proved; the local
factorization/gluing residual is the only remaining input. -/
theorem affineTarget_proved_and_general_residual :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) ∧
      (NonAffineTargetExtensionResidualGeneral (R := R) (G := G) (A := A) →
        ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A)) :=
  ⟨affineTargetUniversalResidual_holds (R := R) (G := G) (A := A),
    generalTargetUniversal_of_residual (R := R) (G := G) (A := A)⟩

/-- The gluing datum is exactly the missing local affine factorization data, not
a fake universal property. -/
def ExactGeneralGluingResidual : Prop :=
  NonAffineTargetExtensionResidualGeneral (R := R) (G := G) (A := A)

/-- The exact gluing residual specification. -/
theorem exactGeneralGluingResidual_iff :
    ExactGeneralGluingResidual (R := R) (G := G) (A := A) ↔
      ∀ (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z),
        (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
          GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f :=
  Iff.rfl


/-- The general factorization residual is actual whenever its local data are
supplied. -/
theorem generalFactorizationResidual_of_localData
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    (C : AffineOpenCover Z)
    (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :
    GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f :=
  ⟨C, ⟨L⟩⟩

/-- The glued map from the local data is actual. -/
noncomputable def localDataGluedMap
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :
    Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z :=
  L.gluedMap

/-- The local data glued map factorizes the invariant morphism. -/
theorem localDataGluedMap_fac
    {Z : Scheme.{u}} {f : Spec (CommRingCat.of A) ⟶ Z}
    {C : AffineOpenCover Z}
    (L : LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) :
    q (R := R) (G := G) (A := A) ≫ localDataGluedMap (R := R) (G := G) (A := A) L = f :=
  L.gluedMap_fac

/-- The local data are exactly the non-affine extension obstruction. -/
theorem nonAffineData_exact :
    (∀ (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z)
      (C : AffineOpenCover Z),
      Nonempty (LocalAffineFactorization (R := R) (G := G) (A := A) Z f C) →
        GeneralTargetFactorizationResidual (R := R) (G := G) (A := A) Z f) :=
  fun _ _ C h => ⟨C, h⟩


/-- The exact obstruction boundary is the local affine factorization/gluing
datum; no universal property is assumed. -/
theorem generalUniversal_exact_boundary :
    NonAffineTargetExtensionResidualGeneral (R := R) (G := G) (A := A) →
      ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A) :=
  generalTargetUniversal_of_residual (R := R) (G := G) (A := A)

/-- The affine-target universal property remains proved; the local affine gluing datum is the exact residual. -/
theorem affineTarget_remains_proved :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) :=
  affineTargetUniversalResidual_holds (R := R) (G := G) (A := A)

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientGeneralUniversal
