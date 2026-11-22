import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.ABCBridge.CoverSectionsAction

noncomputable section

namespace ABCBridge.AffineQuotientActionDataFromCover

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable (X : FiniteEtaleCover (Spec (CommRingCat.of R)))

/-- The coordinate algebra of a finite etale cover. -/
abbrev CoverCoordinateAlgebra : Type u := CoverSections X

/-- Its production R-algebra structure. -/
noncomputable abbrev coverCoordinateAlgebra : Algebra R (CoverCoordinateAlgebra X) :=
  coverSectionsAlgebra X

/-- The affine finite-etale quotient package for an actual cover action. -/
noncomputable def affineFiniteEtaleQuotientFromCover
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) :
    letI := hact
    letI := hcomm
    AffineFiniteEtaleQuotient (R := R) (G := G) (A := CoverCoordinateAlgebra X) :=
  letI := hact
  letI := hcomm
  affineFiniteEtaleQuotient (R := R) (G := G) (A := CoverCoordinateAlgebra X)

/-- The quotient scheme Spec of the fixed-point subalgebra. -/
noncomputable def coverQuotientScheme
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) : Scheme.{u} :=
  letI := hact
  letI := hcomm
  affineQuotientScheme (R := R) (G := G) (A := CoverCoordinateAlgebra X)

/-- The quotient projection from Spec Γ(X). -/
noncomputable def coverCoordinateProjection
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) :
    Spec (CommRingCat.of (CoverCoordinateAlgebra X)) ⟶
      coverQuotientScheme X hact hcomm :=
  letI := hact
  letI := hcomm
  affineQuotientProjection (R := R) (G := G) (A := CoverCoordinateAlgebra X)

/-- The same projection on the original carrier, through isoSpec. -/
noncomputable def coverProjectionFromCarrier
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) :
    X.carrier ⟶ coverQuotientScheme X hact hcomm :=
  X.carrier.isoSpec.hom ≫ coverCoordinateProjection X hact hcomm

/-- The package projection is the canonical quotient projection. -/
theorem affineFiniteEtaleQuotientFromCover_projection
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) :
    letI := hact
    letI := hcomm
    (affineFiniteEtaleQuotientFromCover X hact hcomm).projection =
      affineQuotientProjection (R := R) (G := G) (A := CoverCoordinateAlgebra X) :=
  rfl

/-- The carrier projection factors through isoSpec and the package projection. -/
theorem coverProjectionFromCarrier_eq
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) :
    letI := hact
    letI := hcomm
    coverProjectionFromCarrier X hact hcomm =
      X.carrier.isoSpec.hom ≫
        (affineFiniteEtaleQuotientFromCover X hact hcomm).projection :=
  rfl

/-- The quotient projection is invariant under the transported action. -/
theorem coverCoordinateProjection_invariant
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X)) (g : G) :
    letI := hact
    letI := hcomm
    specAction (R := R) (G := G) (A := CoverCoordinateAlgebra X) g ≫
        coverCoordinateProjection X hact hcomm =
      coverCoordinateProjection X hact hcomm :=
  letI := hact
  letI := hcomm
  affineQuotientProjection_invariant (R := R) (G := G) (A := CoverCoordinateAlgebra X) g

/-- The affine-target universal property for the cover quotient. -/
theorem coverCoordinateProjection_universal
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X))
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (CoverCoordinateAlgebra X)) ⟶
      Spec (CommRingCat.of B))
    (hf : ∀ g : G,
      letI := hact
      letI := hcomm
      specAction (R := R) (G := G) (A := CoverCoordinateAlgebra X) g ≫ f = f) :
    ∃! v : coverQuotientScheme X hact hcomm ⟶ Spec (CommRingCat.of B),
      coverCoordinateProjection X hact hcomm ≫ v = f :=
  letI := hact
  letI := hcomm
  affineQuotientUniversal (R := R) (G := G) (A := CoverCoordinateAlgebra X) B f hf

/-- The package universal property, restated for the cover. -/
theorem affineFiniteEtaleQuotientFromCover_universal
    (hact : MulSemiringAction G (CoverCoordinateAlgebra X))
    (hcomm : SMulCommClass G R (CoverCoordinateAlgebra X))
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (CoverCoordinateAlgebra X)) ⟶
      Spec (CommRingCat.of B))
    (hf : ∀ g : G,
      letI := hact
      letI := hcomm
      specAction (R := R) (G := G) (A := CoverCoordinateAlgebra X) g ≫ f = f) :
    letI := hact
    letI := hcomm
    ∃! v : coverQuotientScheme X hact hcomm ⟶ Spec (CommRingCat.of B),
      (affineFiniteEtaleQuotientFromCover X hact hcomm).projection ≫ v = f :=
  letI := hact
  letI := hcomm
  (affineFiniteEtaleQuotientFromCover X hact hcomm).universal B f hf


section ActualCoverAction

variable (act : G →* CategoryTheory.Aut X)

/-- The actual induced action on the cover coordinate algebra. -/
noncomputable def coverAction : MulSemiringAction G (CoverCoordinateAlgebra X) :=
  coverSectionsMulSemiringAction X act

/-- R-linearity of the actual induced action. -/
noncomputable def coverActionComm :
    letI := coverAction X act
    SMulCommClass G R (CoverCoordinateAlgebra X) :=
  coverSectionsSMulCommClass X act

/-- The actual affine finite-etale quotient package for the cover. -/
noncomputable def actualAffineFiniteEtaleQuotient :
    letI := coverAction X act
    letI := coverActionComm X act
    AffineFiniteEtaleQuotient (R := R) (G := G) (A := CoverCoordinateAlgebra X) :=
  affineFiniteEtaleQuotientFromCover X (coverAction X act) (coverActionComm X act)

/-- The actual quotient scheme. -/
noncomputable def actualQuotientScheme : Scheme.{u} :=
  coverQuotientScheme X (coverAction X act) (coverActionComm X act)

/-- The actual quotient projection from the coordinate Spectrum. -/
noncomputable def actualCoordinateProjection :
    Spec (CommRingCat.of (CoverCoordinateAlgebra X)) ⟶ actualQuotientScheme X act :=
  coverCoordinateProjection X (coverAction X act) (coverActionComm X act)

/-- The actual quotient projection from the original carrier. -/
noncomputable def actualCarrierProjection :
    X.carrier ⟶ actualQuotientScheme X act :=
  coverProjectionFromCarrier X (coverAction X act) (coverActionComm X act)

/-- The actual carrier projection is isoSpec followed by the actual coordinate
projection. -/
theorem actualCarrierProjection_eq :
    actualCarrierProjection X act =
      X.carrier.isoSpec.hom ≫ actualCoordinateProjection X act :=
  rfl

/-- The actual package projection is the actual coordinate projection. -/
theorem actualAffineFiniteEtaleQuotient_projection :
    letI := coverAction X act
    letI := coverActionComm X act
    (actualAffineFiniteEtaleQuotient X act).projection =
      actualCoordinateProjection X act :=
  rfl

/-- Invariance of the actual coordinate projection. -/
theorem actualCoordinateProjection_invariant (g : G) :
    letI := coverAction X act
    letI := coverActionComm X act
    specAction (R := R) (G := G) (A := CoverCoordinateAlgebra X) g ≫
        actualCoordinateProjection X act =
      actualCoordinateProjection X act :=
  coverCoordinateProjection_invariant X (coverAction X act) (coverActionComm X act) g

/-- Universal property of the actual cover quotient. -/
theorem actualCoordinateProjection_universal
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (CoverCoordinateAlgebra X)) ⟶
      Spec (CommRingCat.of B))
    (hf : ∀ g : G,
      letI := coverAction X act
      letI := coverActionComm X act
      specAction (R := R) (G := G) (A := CoverCoordinateAlgebra X) g ≫ f = f) :
    ∃! v : actualQuotientScheme X act ⟶ Spec (CommRingCat.of B),
      actualCoordinateProjection X act ≫ v = f :=
  coverCoordinateProjection_universal X (coverAction X act) (coverActionComm X act) B f hf

end ActualCoverAction

end ABCBridge.AffineQuotientActionDataFromCover
