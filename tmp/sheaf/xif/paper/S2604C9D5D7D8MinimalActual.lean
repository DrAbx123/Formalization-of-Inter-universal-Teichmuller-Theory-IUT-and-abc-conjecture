import tmp.sheaf.xif.paper.S1908S1280D5ImageActual
import tmp.sheaf.xif.paper.S1320SectionsCuspActual
import tmp.sheaf.xif.paper.S2603D5D7D8DependencyActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S2604C9D5D7D8MinimalActual

open LeanFormal.IUT.XiFPaper.S1908S1280D5ImageActual
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

/-- Minimal D5 data: exactly the S1894/S1908 exact missing image input on the S1280 Gaussian curve. -/
def S2604D5Data (l : PrimeGeFive) : Prop := S1908ExactMissing l

/-- D5 is exactly the paper's large-image field `SerreStyleLargeImageStatement`. -/
theorem S2604D5Data_iff_serre (l : PrimeGeFive) :
    S2604D5Data l ↔ S1298LargeImageField l :=
  S1908ExactMissing_iff_serre l

/-- Minimal D7 data: first field `localGroupCarrier` together with the S1320 tail. -/
abbrev S2604D7Data (l : PrimeGeFive) : Type 1 :=
  Σ G0 : S1320D7FirstField l, S1320D7Tail l G0

theorem S2604D7Data_nonempty_iff (l : PrimeGeFive) :
    Nonempty (D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) ↔
      ∃ G0 : S1320D7FirstField l, Nonempty (S1320D7Tail l G0) :=
  S1320D7Supply_nonempty_iff_firstField_tail l

/-- Minimal D8 data: real cusp coordinate plus the S1320 cusp tail. -/
abbrev S2604D8Data : Type := Σ e : S1320CuspFirstField, S1320CuspTail e

theorem S2604D8Data_nonempty_iff :
    Nonempty SourceCuspClause ↔
      ∃ e : S1320CuspFirstField, Nonempty (S1320CuspTail e) :=
  S1320CuspClause_nonempty_iff_firstField_tail

/-- The exact D5 obstruction: the current D5 input is the S1908 large-image input, which is not inhabited in the tree. -/
theorem S2604D5Data_iff_imageContainsSL2 (l : PrimeGeFive) :
    S2604D5Data l ↔ S1298LargeImageField l :=
  S2604D5Data_iff_serre l

end LeanFormal.IUT.XiFPaper.S2604C9D5D7D8MinimalActual

end