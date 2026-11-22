import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D line-bundle interface consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DLineBundleInterfaceConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleInterfaceActual

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  {F : Type w} [Field F] [Algebra R F]

theorem dLineBundleInterfaceConsumer_finrank (L : LineBundlePullbackInterface R A F) :
    Module.finrank R L.functionFieldSections = L.m :=
  finrank_functionFieldSections_eq L

theorem dLineBundleInterfaceConsumer_degreeImage (L : LineBundlePullbackInterface R A F) :
    (L.iso ⟨L.f, L.f_mem⟩ : F) ∈ L.functionFieldSections :=
  sectionImage_mem L

def dLineBundleInterfaceConsumerRows : List (String × String × String) :=
  [ ("finrank = m", "PROVED", "dLineBundleInterfaceConsumer_finrank"),
    ("section image in function-field sections", "PROVED", "dLineBundleInterfaceConsumer_degreeImage") ]

theorem dLineBundleInterfaceConsumerRows_length : dLineBundleInterfaceConsumerRows.length = 2 := rfl

#check dLineBundleInterfaceConsumer_finrank
#check dLineBundleInterfaceConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DLineBundleInterfaceConsumerActual
end