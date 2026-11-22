import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEHDDDataActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Input Label Choice)
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S1300SHEHDDData : Type where
  hdd : S1215HDDLocalLattice (I := I)
  rank : Nat
  rank_eq : hdd.rank = rank
  logShift : ∀ (m m' : Int) (j : SignedLabel l.value),
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)

noncomputable def S1300SHEHDDData.of
    (D : S1300HDDHullDetSource I) : S1300SHEHDDData I J where
  hdd := D.toS1215 (I := I)
  rank := D.rank
  rank_eq := rfl
  logShift := s1215LogShiftReadoutCompat_actual J

#check S1300SHEHDDData
#check S1300SHEHDDData.of
end LeanFormal.IUT.XiFPaper.S1300SHEHDDDataActual
end
