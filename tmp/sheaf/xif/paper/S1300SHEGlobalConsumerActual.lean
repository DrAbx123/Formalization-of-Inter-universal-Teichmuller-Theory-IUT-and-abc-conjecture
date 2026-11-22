import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEGlobalConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Input Label Choice)
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Consumer using S1300, S1204 and S1385 actual donors, without importing
S1215: SHE log-shift + actual frozen hull/det spec. -/
theorem S1300SHEGlobalConsumer
    (D : S1300HDDHullDetSource I) :
    (∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)) ∧
    HullDeterminantLogVolumeFrozenSpec := by
  refine ⟨?_, s1385FrozenSpec_actual⟩
  intro m m' j
  simpa [oneColumnLogReadout] using oneColumnLogReadout_shift J m m' j

#check S1300SHEGlobalConsumer
end LeanFormal.IUT.XiFPaper.S1300SHEGlobalConsumerActual
end
