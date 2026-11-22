import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

namespace Probe4

abbrev R : Type := S1726CoordinateRing
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

#check @CategoryTheory.op_id
#check @CategoryTheory.op_comp
#check @CategoryTheory.unop_comp
#check @CategoryTheory.op_inj
#check @Quiver.Hom.op_inj
#check @CommRingCat.ofHom_id
#check @CommRingCat.ofHom_comp
#check @CommRingCat.hom_ofHom
#check @CommAlgCat.id_hom
#check @CommAlgCat.comp_hom
#check @CommAlgCat.hom_ext
#check @InducedCategory.id_hom
#check @InducedCategory.comp_hom
#check @InducedCategory.hom_ext
#check @AlgHom.comp_toRingHom
#check @AlgHom.toRingHom_eq_coe
#check @ObjectProperty.FullSubcategory
#check @ObjectProperty.ι

-- understand the commutation goal
example {A B : Algᵒᵖ} (g : A ⟶ B) (x : R) : True := by
  have h := (g.unop.hom.hom).commutes x
  trivial

end Probe4
