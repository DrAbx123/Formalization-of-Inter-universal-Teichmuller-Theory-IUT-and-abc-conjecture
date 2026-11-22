import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u
variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable {W : EtaleStackPseudofunctor S1726K}

example {a b : Pseudofunctor.StrongTrans W X} (e : a ≅ b) :
    𝟙 a ≫ e.hom = e.hom := by
  exact Category.id_comp e.hom

example {a b : Pseudofunctor.StrongTrans W X} (e : a ≅ b) :
    𝟙 a ≫ e.hom = e.hom := by
  rw [Category.id_comp]

end Probe
