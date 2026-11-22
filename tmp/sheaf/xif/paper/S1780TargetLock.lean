import tmp.sheaf.xif.paper.S1780GeometricFiberFintypeActual

noncomputable section
namespace S1780TargetLock

open LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper

#check @S1780BaseChange
#check @S1780Model
#check @S1780ModelOver
#check @S1780Model_finiteEtale
#check @S1780BaseEndomorphism_subsingleton
#check @S1780SubsingletonAlgHomOfField
#check @S1780AlgHomFintype
#check @S1780SectionToFiber
#check @S1780SectionFintype
#check @S1780FiberCovered
#check @S1780FirstMissing
#check @S1780FintypeRequired_of_comparison
#check @S1780FintypeRequired_of_firstMissing

/-- Target lock: the reduction produces exactly the S1735 requirement. -/
example (hfin : ∀ cover : S1735Cover, S1780SectionFintype cover)
    (hcov : ∀ cover : S1735Cover, S1780FiberCovered cover) :
    S1735GeometricFiberFintypeRequired :=
  S1780FintypeRequired_of_comparison hfin hcov

/-- Target lock: the comparison map really lands in the S1735 literal fiber. -/
example (cover : S1735Cover) (s : S1735BaseScheme ⟶ S1780Model cover) :
    S1735Fiber cover :=
  S1780SectionToFiber cover s

end S1780TargetLock
