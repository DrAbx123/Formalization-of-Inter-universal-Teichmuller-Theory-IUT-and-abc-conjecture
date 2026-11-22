import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeAction

/-!
# Affine finite-etale quotient consumer for the regular permutation cover

Instantiates the affine finite-etale quotient package for the actual regular
permutation cover Spec (G -> R).  The coordinate algebra is identified with
(G -> R), the quotient is Spec ((G -> R)^G), the projection is the fixed-point
inclusion, and the quotient scheme is identified with the production regular
quotient cover.  No residual and no fabricated quotient are introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.ABCBridge.FiniteEtaleQuotientFreeAction
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace ABCBridge.AffineFiniteEtaleQuotientConsumer

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- The regular permutation cover's sections are the permutation algebra. -/
noncomputable def regularPermutationSectionsRingEquiv :
    Γ((regularPermutationCover (R := R) (G := G)).carrier, ⊤) ≃+* (G → R) :=
  (Scheme.ΓSpecIso (CommRingCat.of (G → R))).commRingCatIsoToRingEquiv

/-- The quotient scheme is the fixed-point spectrum of the permutation algebra. -/
theorem regularQuotientScheme_eq_affineQuotientScheme :
    (regularQuotientCover (R := R) (G := G)).carrier =
      affineQuotientScheme (R := R) (G := G) (G → R) :=
  rfl

/-- The actual affine finite-etale quotient package for the regular cover. -/
noncomputable def regularAffineFiniteEtaleQuotientPackage :
    AffineFiniteEtaleQuotient (R := R) (G := G) (G → R) :=
  affineFiniteEtaleQuotient (R := R) (G := G) (G → R)

/-- The projection is invariant under the regular permutation action. -/
theorem regularAffineFiniteEtaleQuotientPackage_invariant (g : G) :
    specAction (R := R) (G := G) (A := G → R) g ≫
        (regularAffineFiniteEtaleQuotientPackage R G).projection =
      (regularAffineFiniteEtaleQuotientPackage R G).projection :=
  (regularAffineFiniteEtaleQuotientPackage R G).invariant g

/-- Affine-target universal property for G-invariant morphisms out of the
regular permutation cover. -/
theorem regularAffineFiniteEtaleQuotientPackage_universal
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (G → R)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := G → R) g ≫ f = f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
        Spec (CommRingCat.of B),
      (regularAffineFiniteEtaleQuotientPackage R G).projection ≫ u = f :=
  (regularAffineFiniteEtaleQuotientPackage R G).universal B f hf

/-- The regular quotient cover is finite etale over R (free regular action). -/
theorem regularAffineFiniteEtaleQuotientPackage_finiteEtale :
    Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  regularAffineFiniteEtaleQuotientCover_complete |>.2

/-- The quotient cover is identified with the production regular quotient cover. -/
theorem regularAffineFiniteEtaleQuotientPackage_quotientCover :
    (regularAffineFiniteEtaleQuotientCover (R := R) (G := G)).quotientCover =
      regularQuotientCover (R := R) (G := G) :=
  regularAffineFiniteEtaleQuotientCover_quotientCover

/-- The actual quotient scheme of the regular cover is the production quotient
cover's carrier. -/
theorem regularAffineFiniteEtaleQuotientPackage_quotientScheme :
    affineQuotientScheme (R := R) (G := G) (G → R) =
      (regularQuotientCover (R := R) (G := G)).carrier :=
  (regularQuotientScheme_eq_affineQuotientScheme R G).symm

/-- Final consumer: sections, quotient, projection, invariance, affine-target
universality, finiteness/etaleness, and identification with the production
regular quotient cover. -/
theorem regularAffineFiniteEtaleQuotientConsumer
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (G → R)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := G → R) g ≫ f = f) :
    (Nonempty (Γ((regularPermutationCover (R := R) (G := G)).carrier, ⊤) ≃+* (G → R))) ∧
      (affineQuotientScheme (R := R) (G := G) (G → R) =
        (regularQuotientCover (R := R) (G := G)).carrier) ∧
      (∃! u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
          Spec (CommRingCat.of B),
        (regularAffineFiniteEtaleQuotientPackage R G).projection ≫ u = f) ∧
      Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  ⟨⟨regularPermutationSectionsRingEquiv R G⟩,
    regularAffineFiniteEtaleQuotientPackage_quotientScheme R G,
    regularAffineFiniteEtaleQuotientPackage_universal R G B f hf,
    regularAffineFiniteEtaleQuotientCover_etale,
    regularAffineFiniteEtaleQuotientCover_finite⟩

/-- Projection consumer in primitive form. -/
theorem regularAffineFiniteEtaleQuotientProjection_consumer :
    ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          (regularAffineFiniteEtaleQuotientPackage R G).projection =
        (regularAffineFiniteEtaleQuotientPackage R G).projection :=
  regularAffineFiniteEtaleQuotientPackage_invariant R G

/-- The regular permutation cover carrier is the spectrum of the permutation
algebra. -/
theorem regularPermutationCover_carrier_eq :
    (regularPermutationCover (R := R) (G := G)).carrier =
      Spec (CommRingCat.of (G → R)) :=
  rfl

/-- The finite-etale quotient package projection is the affine quotient map. -/
theorem regularAffineFiniteEtaleQuotientPackage_projection_eq :
    (regularAffineFiniteEtaleQuotientPackage R G).projection =
      affineQuotientProjection (R := R) (G := G) (G → R) :=
  (regularAffineFiniteEtaleQuotientPackage R G).projection_eq

/-- The regular quotient cover carrier is the affine quotient scheme. -/
theorem regularQuotientCover_carrier_eq :
    (regularQuotientCover (R := R) (G := G)).carrier =
      affineQuotientScheme (R := R) (G := G) (G → R) :=
  regularQuotientScheme_eq_affineQuotientScheme R G

/-- The universal factor for the regular quotient cover. -/
noncomputable def regularAffineFiniteEtaleQuotientFactor
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (G → R)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := G → R) g ≫ f = f) :
    affineQuotientScheme (R := R) (G := G) (G → R) ⟶
      Spec (CommRingCat.of B) :=
  (regularAffineFiniteEtaleQuotientPackage R G).universal B f hf |>.choose

theorem regularAffineFiniteEtaleQuotientFactor_fac
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (G → R)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := G → R) g ≫ f = f) :
    (regularAffineFiniteEtaleQuotientPackage R G).projection ≫
        regularAffineFiniteEtaleQuotientFactor R G B f hf = f :=
  (regularAffineFiniteEtaleQuotientPackage R G).universal B f hf |>.choose_spec.1

theorem regularAffineFiniteEtaleQuotientFactor_uniq
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (G → R)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := G → R) g ≫ f = f)
    (u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
      Spec (CommRingCat.of B))
    (hu : (regularAffineFiniteEtaleQuotientPackage R G).projection ≫ u = f) :
    u = regularAffineFiniteEtaleQuotientFactor R G B f hf :=
  (regularAffineFiniteEtaleQuotientPackage R G).universal B f hf |>.choose_spec.2 u hu

end ABCBridge.AffineFiniteEtaleQuotientConsumer
