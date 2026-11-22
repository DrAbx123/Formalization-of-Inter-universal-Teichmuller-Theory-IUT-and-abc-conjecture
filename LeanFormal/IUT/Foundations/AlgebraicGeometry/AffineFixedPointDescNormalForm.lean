import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.IsospecSectionsCoherence
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Normal form for the affine fixed-point quotient descent

For an invariant `R`-algebra map `φ : B →ₐ[R] A`, the unique lifted map
`ψ : B →ₐ[R] A^G` with `fixedPointInclusion.comp ψ = φ` is packaged together with
its `R`-algebra compatibility.  This gives the algebra square needed by the
`desc`/`w` construction without going through `Spec.preimage`.
-/
namespace ABCBridge.AffineFixedPointDescNormalForm

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

universe u

variable {R A B G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]
  [CommRing B] [Algebra R B]

/-- The unique lift of an invariant map to the fixed-point subalgebra, with its
`R`-algebra compatibility. -/
theorem exists_affineFixedPointLiftAlgHom
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃ ψ : B →ₐ[R] fixedPointSubalgebra R A G,
      (fixedPointInclusion R A G).comp ψ = φ ∧
        ψ.toRingHom.comp (algebraMap R B) =
          algebraMap R (fixedPointSubalgebra R A G) := by
  obtain ⟨ψ, hψ, -⟩ :=
    ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
      R A G φ hφ
  refine ⟨ψ, hψ, ?_⟩
  apply RingHom.ext
  intro r
  apply Subtype.val_injective
  have h1 := AlgHom.congr_fun hψ (algebraMap R B r)
  change fixedPointInclusion R A G (ψ ((algebraMap R B) r)) =
    φ ((algebraMap R B) r) at h1
  change fixedPointInclusion R A G (ψ ((algebraMap R B) r)) =
    fixedPointInclusion R A G ((algebraMap R (fixedPointSubalgebra R A G)) r)
  rw [h1, AlgHom.commutes]
  exact (fixedPointInclusion R A G).commutes r

/-- The inverse affine chart followed by the structure map is the section-map
affine structure. -/
theorem isoSpec_inv_structureMap
    {Z : LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover
      (Spec (CommRingCat.of R))} :
    Z.carrier.isoSpec.inv ≫ Z.structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z.carrier, ⊤))) := by
  have h := ABCBridge.IsospecSectionsCoherence.isoSpec_sectionsAlgebraMap (R := R) Z
  rw [← h]
  rw [Iso.inv_hom_id_assoc]

/-- The affine descent map `Spec (A^G) → Z` attached to a lifted algebra map. -/
noncomputable def descSchemeMap
    {Z : LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover
      (Spec (CommRingCat.of R))}
    (ψ : Γ(Z.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R A G) :
    Spec (CommRingCat.of (fixedPointSubalgebra R A G)) ⟶ Z.carrier :=
  Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Z.carrier.isoSpec.inv

/-- The `w` square for the affine descent map. -/
theorem descSchemeMap_structureMap
    {Z : LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover
      (Spec (CommRingCat.of R))}
    (ψ : Γ(Z.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R A G)
    (hψ : ψ.toRingHom.comp (algebraMap R Γ(Z.carrier, ⊤)) =
      algebraMap R (fixedPointSubalgebra R A G)) :
    descSchemeMap (R := R) (A := A) (G := G) ψ ≫ Z.structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (fixedPointSubalgebra R A G))) := by
  rw [descSchemeMap, Category.assoc, isoSpec_inv_structureMap]
  rw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom hψ)

end ABCBridge.AffineFixedPointDescNormalForm