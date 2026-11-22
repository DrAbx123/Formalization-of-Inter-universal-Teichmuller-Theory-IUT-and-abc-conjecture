import tmp.sheaf.xif.paper.S3129FiniteEtaleCompositionAttempt
noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S3129FiniteEtaleCompositionAttempt
namespace LeanFormal.IUT.XiFPaper.S3129ProbeComp

noncomputable def attempt (F : Type) [Field F] : S3129CompositionTarget F := by
  intro W Y Z f g Mf Mg
  refine { baseChange := ?_, hasProperty := ?_ }

end LeanFormal.IUT.XiFPaper.S3129ProbeComp
end