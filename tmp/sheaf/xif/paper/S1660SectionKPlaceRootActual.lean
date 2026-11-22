import tmp.sheaf.xif.paper.S1647RouteARootActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1647RouteARootActual
namespace LeanFormal.IUT.XiFPaper.S1660SectionKPlaceRootActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
abbrev Kv : Type _ := Completion (sectionKPlace T b)
structure S1660UnitRootDescentData where
  uniformizer : Kv T b
  uniformizer_ne_zero : uniformizer ≠ 0
  t : ℤ
  order_eq : (sectionQ T b).order = (2 * l.value) * t
  unit : Kv T b
  unit_ne_zero : unit ≠ 0
  q_decomp : (sectionQ T b).q = unit * uniformizer ^ ((2 * l.value) * t)
  unit_root : Kv T b
  unit_root_ne_zero : unit_root ≠ 0
  unit_root_pow : unit_root ^ (2 * l.value) = unit
noncomputable def s1660Root (D : S1660UnitRootDescentData T b) : Kv T b :=
  D.unit_root * D.uniformizer ^ D.t
theorem s1660Root_ne_zero (D : S1660UnitRootDescentData T b) :
    s1660Root T b D ≠ 0 := by
  unfold s1660Root
  exact mul_ne_zero D.unit_root_ne_zero (zpow_ne_zero D.t D.uniformizer_ne_zero)
theorem s1660Root_pow (D : S1660UnitRootDescentData T b) :
    s1660Root T b D ^ (2 * l.value) = (sectionQ T b).q := by
  unfold s1660Root
  rw [mul_pow, D.unit_root_pow, D.q_decomp]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring
noncomputable def s1660RootCard (D : S1660UnitRootDescentData T b) :
    QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b) :=
  QParameterTwoLRootCard.ofRoot (s1660Root T b D) (s1660Root_ne_zero T b D)
    (s1660Root_pow T b D)
theorem s1660SectionKPlaceTwoLRoot_of_unitRoot
    (D : S1660UnitRootDescentData T b) :
    SectionKPlaceTwoLRootRequired (T := T) (b := b) :=
  ⟨s1660RootCard T b D⟩
#check S1660UnitRootDescentData
#check s1660RootCard
#check s1660SectionKPlaceTwoLRoot_of_unitRoot
theorem s1660Order_eq_of_dvd (h : (2 * (l.value : ℤ)) ∣ (sectionQ T b).order) :
    ∃ t : ℤ, (sectionQ T b).order = (2 * (l.value : ℤ)) * t := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by simpa [mul_comm] using ht⟩
end LeanFormal.IUT.XiFPaper.S1660SectionKPlaceRootActual

end
