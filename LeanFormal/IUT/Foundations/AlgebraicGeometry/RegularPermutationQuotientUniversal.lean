import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientConsumer

/-!
# Universal property of the regular permutation quotient cover

Consumes the affine finite-etale quotient consumer for the regular permutation
cover.  For a finite-etale cover Z and a G-invariant affine map determined by a
cover morphism from the regular cover, the coordinate algebra of Z is affine,
so the affine quotient universal property factors the morphism uniquely through
the fixed-point quotient.  The quotient is identified with the production
regular quotient cover.  No residual and no fabricated factor are introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.ABCBridge.AffineFiniteEtaleQuotientConsumer
open _root_.ABCBridge.FiniteEtaleQuotientFreeAction
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace ABCBridge.RegularPermutationQuotientUniversal

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- The actual carrier map underlying a cover morphism. -/
noncomputable def coverCarrierMap
    {Z : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z) :
    (regularPermutationCover (R := R) (G := G)).carrier ⟶ Z.carrier :=
  (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left

/-- The coordinate isomorphism from the regular cover carrier to the
permutation algebra spectrum. -/
noncomputable def regularCoverCoordinateIso :
    (regularPermutationCover (R := R) (G := G)).carrier ≅
      Spec (CommRingCat.of (G → R)) :=
  (Scheme.isoSpec (regularPermutationCover (R := R) (G := G)).carrier).trans
    (Scheme.Spec.mapIso (Scheme.ΓSpecIso (CommRingCat.of (G → R))).op).symm

/-- The coordinate isomorphism from an affine cover target to its section
spectrum. -/
noncomputable def coverTargetCoordinateIso
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    Z.carrier ≅ Spec Γ(Z.carrier, ⊤) :=
  Scheme.isoSpec Z.carrier

/-- The affine map associated to a cover morphism from the regular cover. -/
noncomputable def regularCoverAffineMap
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z) :
    Spec (CommRingCat.of (G → R)) ⟶ Spec Γ(Z.carrier, ⊤) :=
  (regularCoverCoordinateIso R G).inv ≫ coverCarrierMap R G f ≫
    (coverTargetCoordinateIso R Z).hom

/-- The regular quotient cover carrier is the affine quotient spectrum. -/
theorem regularQuotientCover_carrier_affineQuotient :
    (regularQuotientCover (R := R) (G := G)).carrier =
      affineQuotientScheme (R := R) (G := G) (G → R) :=
  regularQuotientScheme_eq_affineQuotientScheme R G

/-- The regular quotient cover carrier is affine. -/
theorem regularQuotientCover_carrier_affine :
    IsAffine (regularQuotientCover (R := R) (G := G)).carrier :=
  finiteEtaleCoverCarrier_isAffine R (regularQuotientCover (R := R) (G := G))

/-- Affine universal property for the G-invariant affine map determined by a
cover morphism from the regular cover. -/
theorem regularCoverAffineUniversal
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
        Spec Γ(Z.carrier, ⊤),
      affineQuotientProjection (R := R) (G := G) (G → R) ≫ u =
        regularCoverAffineMap R G Z f :=
  affineQuotientUniversal (R := R) (G := G) (A := G → R)
    Γ(Z.carrier, ⊤) (regularCoverAffineMap R G Z f) hInv

/-- The unique factorization through the production regular quotient cover
carrier. -/
theorem regularPermutationQuotientUniversal
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
        Spec Γ(Z.carrier, ⊤),
      affineQuotientProjection (R := R) (G := G) (G → R) ≫ u =
        regularCoverAffineMap R G Z f :=
  regularCoverAffineUniversal R G Z f hInv

/-- Final consumer: the quotient identification and the unique factorization. -/
theorem regularPermutationQuotientUniversal_consumer
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f) :
    (regularQuotientCover (R := R) (G := G)).carrier =
        affineQuotientScheme (R := R) (G := G) (G → R) ∧
      (∃! u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
          Spec Γ(Z.carrier, ⊤),
        affineQuotientProjection (R := R) (G := G) (G → R) ≫ u =
          regularCoverAffineMap R G Z f) :=
  ⟨regularQuotientCover_carrier_affineQuotient R G,
    regularPermutationQuotientUniversal R G Z f hInv⟩

/-- The regular cover's sections are the permutation algebra. -/
theorem regularPermutationSectionsRingEquiv_holds :
    Nonempty (Γ((regularPermutationCover (R := R) (G := G)).carrier, ⊤) ≃+* (G → R)) :=
  ⟨regularPermutationSectionsRingEquiv R G⟩

/-- The factorization map chosen by the regular quotient universal property. -/
noncomputable def regularPermutationQuotientFactor
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f) :
    affineQuotientScheme (R := R) (G := G) (G → R) ⟶
      Spec Γ(Z.carrier, ⊤) :=
  (regularCoverAffineUniversal R G Z f hInv).choose

theorem regularPermutationQuotientFactor_fac
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f) :
    affineQuotientProjection (R := R) (G := G) (G → R) ≫
        regularPermutationQuotientFactor R G Z f hInv =
      regularCoverAffineMap R G Z f :=
  (regularCoverAffineUniversal R G Z f hInv).choose_spec.1

theorem regularPermutationQuotientFactor_uniq
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f)
    (u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
      Spec Γ(Z.carrier, ⊤))
    (hu : affineQuotientProjection (R := R) (G := G) (G → R) ≫ u =
      regularCoverAffineMap R G Z f) :
    u = regularPermutationQuotientFactor R G Z f hInv :=
  (regularCoverAffineUniversal R G Z f hInv).choose_spec.2 u hu

theorem regularPermutationQuotientUniversal_factor_consumer
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : regularPermutationCover (R := R) (G := G) ⟶ Z)
    (hInv : ∀ g : G,
      specAction (R := R) (G := G) (A := G → R) g ≫
          regularCoverAffineMap R G Z f =
        regularCoverAffineMap R G Z f) :
    (affineQuotientProjection (R := R) (G := G) (G → R) ≫
        regularPermutationQuotientFactor R G Z f hInv =
      regularCoverAffineMap R G Z f) ∧
      (∀ u : affineQuotientScheme (R := R) (G := G) (G → R) ⟶
          Spec Γ(Z.carrier, ⊤),
        affineQuotientProjection (R := R) (G := G) (G → R) ≫ u =
            regularCoverAffineMap R G Z f →
          u = regularPermutationQuotientFactor R G Z f hInv) :=
  ⟨regularPermutationQuotientFactor_fac R G Z f hInv,
    fun u hu => regularPermutationQuotientFactor_uniq R G Z f hInv u hu⟩

theorem regularQuotientCover_carrier_eq_affineQuotientScheme :
    (regularQuotientCover (R := R) (G := G)).carrier =
      affineQuotientScheme (R := R) (G := G) (G → R) :=
  regularQuotientCover_carrier_affineQuotient R G

end ABCBridge.RegularPermutationQuotientUniversal
