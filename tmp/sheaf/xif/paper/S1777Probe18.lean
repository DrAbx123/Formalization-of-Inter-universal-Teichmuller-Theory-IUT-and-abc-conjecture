import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe18

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @ConcreteCategory.isIso_iff_bijective
#check @RingHom.StableUnderComposition
#check @RingHom.Etale.stableUnderComposition
#check @RingHom.Etale.stableUnderComposition.comp
#check @RingHom.StableUnderComposition.comp
#check @RingHom.algebraMap_toAlgebra
#check @HasAffineProperty.iff_of_isAffine
#check @Scheme.Hom.appTop
#check @Scheme.Γ

/-- The algebra map R' -> Γ(Spec X.left) -> ... : the global-sections algebra. -/
noncomputable def algMap (X : S1733Slice) : CommRingCat.of R ⟶ X.left.unop :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom

/-- The spectrum of the algebra map is the original structure morphism. -/
theorem Spec_map_algMap (X : S1733Slice) :
    Spec.map (algMap X).hom = X.hom := by
  have h := Scheme.isoSpec_hom_naturality X.hom
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_hom] at h
  rw [← Spec.map_comp] at h
  show Spec.map ((algMap X).hom) = X.hom
  rw [algMap, CommRingCat.comp_apply', CommRingCat.comp_apply', Spec.map_comp, Spec.map_comp,
    Spec.map_inv, ← h, Iso.inv_hom_id_assoc]

end Probe18
