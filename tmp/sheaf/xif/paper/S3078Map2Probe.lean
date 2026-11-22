import tmp.sheaf.xif.paper.S3078QPrimePseudofunctorTarget
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3078QPrimePseudofunctorTarget
namespace P
#check CategoryTheory.LocallyDiscrete.eq_of_hom
#check eqToHom
variable {U V : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)} {f g : U ⟶ V} (η : f ⟶ g)
noncomputable def m2 : S3078Map f ⟶ S3078Map g :=
  eqToHom (congrArg S3078Map (CategoryTheory.LocallyDiscrete.eq_of_hom η))
#check m2
end P
end
