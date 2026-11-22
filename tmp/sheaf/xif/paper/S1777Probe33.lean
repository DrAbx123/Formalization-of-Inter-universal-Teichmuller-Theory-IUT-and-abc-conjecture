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
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe33

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1726AffineScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

noncomputable def algMap (X : S1733Slice) : CommRingCat.of R ⟶ X.left.unop :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop ≫ (Scheme.ΓSpecIso X.left.unop).hom

theorem Spec_map_algMap (X : S1733Slice) : Spec.map (algMap X) = X.hom := by
  have h0 := Scheme.isoSpec_hom_naturality X.hom
  have h : (Spec X.left.unop).isoSpec.hom ≫ Spec.map X.hom.appTop =
      X.hom ≫ (Spec (CommRingCat.of R)).isoSpec.hom := h0
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_hom] at h
  rw [← Spec.map_comp] at h
  have hominv : Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [algMap, Spec.map_comp, Spec.map_comp, ← h, Category.assoc, hominv, Category.comp_id]

end Probe33
