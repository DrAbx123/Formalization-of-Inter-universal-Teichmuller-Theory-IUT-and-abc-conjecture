import tmp.sheaf.xif.paper.S1668UnitRootDescentActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1647RouteARootActual
open LeanFormal.IUT.XiFPaper.S1660SectionKPlaceRootActual
open LeanFormal.IUT.XiFPaper.S1668UnitRootDescentActual
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
namespace LeanFormal.IUT.XiFPaper.S1677UnitKummerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
theorem s1677QUnitPart_valued :
    (Valued.v (((s1668QUnitPart T b).val).1 : Ksection T b) :
      WithZero (Multiplicative Int)) = 1 := by
  have h := Valuation.Integers.valuation_unit
    (v := (Valued.v : Valuation (Ksection T b) (WithZero (Multiplicative Int))))
    (Valuation.integer.integers (Valued.v :
      Valuation (Ksection T b) (WithZero (Multiplicative Int))))
    (s1668QUnitPart T b)
  change (Valued.v (((s1668QUnitPart T b).val).1 : Ksection T b) :
    WithZero (Multiplicative Int)) = 1 at h
  exact h
theorem s1677Q_valued :
    (Valued.v (sectionQ T b).q : WithZero (Multiplicative Int)) =
      WithZero.exp (-(s1668QExponent T b)) := by
  rw [← s1668QUnit_val T b]
  rw [s1668Q_decomp, map_mul, map_zpow₀, s1668Pi_valued,
    ← WithZero.exp_zsmul, s1677QUnitPart_valued, mul_one]
  congr 1
  simp
theorem s1677Log_q :
    WithZero.log (Valued.v (sectionQ T b).q) =
      -(sectionQ T b).exponent := by
  have hv := (sectionQ T b).valuation_ne_zero
  rw [show Valued.v (sectionQ T b).q =
      ((WithZero.unzero hv : Multiplicative Int) :
        WithZero (Multiplicative Int)) from
    (WithZero.coe_unzero hv).symm]
  unfold FinitePlaceQCandidate.exponent
  change WithZero.log (((WithZero.unzero hv : Multiplicative Int) :
    WithZero (Multiplicative Int))) = - -Multiplicative.toAdd (WithZero.unzero hv)
  rw [show WithZero.log (((WithZero.unzero hv : Multiplicative Int) :
    WithZero (Multiplicative Int))) = Multiplicative.toAdd (WithZero.unzero hv) from rfl]
  ring
theorem s1677QExponent_eq_exponent :
    s1668QExponent T b = (sectionQ T b).exponent := by
  have hv := (sectionQ T b).valuation_ne_zero
  have hval : (Valued.v (sectionQ T b).q : WithZero (Multiplicative Int)) =
      WithZero.exp (-(sectionQ T b).exponent) := by
    rw [← WithZero.exp_log hv, s1677Log_q]
  have hm := s1677Q_valued T b
  rw [hval] at hm
  have h := WithZero.exp_inj.mp hm
  linear_combination h
theorem s1677QExponent_eq_order :
    s1668QExponent T b = ((sectionQ T b).order : ℤ) := by
  rw [s1677QExponent_eq_exponent, FinitePlaceQCandidate.order,
    Int.toNat_of_nonneg (le_of_lt (FinitePlaceQCandidate.exponent_pos (sectionQ T b)))]
theorem s1677TwoLDvdExponent
    (h : (2 * (l.value : ℤ)) ∣ ((sectionQ T b).order : ℤ)) :
      (2 * (l.value : ℤ)) ∣ s1668QExponent T b := by
  rwa [s1677QExponent_eq_order]
theorem s1677ExistsT
    (h : (2 * (l.value : ℤ)) ∣ ((sectionQ T b).order : ℤ)) :
      ∃ t : ℤ, s1668QExponent T b = (2 * (l.value : ℤ)) * t := by
  obtain ⟨t, ht⟩ := s1677TwoLDvdExponent (l := l) T b h
  exact ⟨t, ht⟩
def S1677UnitRootRequired : Prop :=
  ∃ v : (Ksection T b)ˣ, v ^ (2 * l.value) = s1668QUnitPartField T b
noncomputable def s1677RootData
    (h : (2 * (l.value : ℤ)) ∣ ((sectionQ T b).order : ℤ))
    (v : (Ksection T b)ˣ)
    (hv : v ^ (2 * l.value) = s1668QUnitPartField T b) :
      S1668UnitRootOnly (l := l) T b := by
  let t := Classical.choose (s1677ExistsT (l := l) T b h)
  exact ⟨t, Classical.choose_spec (s1677ExistsT (l := l) T b h), v, hv⟩
noncomputable def s1677RootCard
    (h : (2 * (l.value : ℤ)) ∣ ((sectionQ T b).order : ℤ))
    (v : (Ksection T b)ˣ)
    (hv : v ^ (2 * l.value) = s1668QUnitPartField T b) :
      QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b) :=
  s1668RootCardFromUnitRoot (l := l) T b (s1677RootData (l := l) T b h v hv)
theorem s1677SectionKPlaceTwoLRoot_of_unitRoot
    (h : (2 * (l.value : ℤ)) ∣ ((sectionQ T b).order : ℤ))
    (v : (Ksection T b)ˣ)
    (hv : v ^ (2 * l.value) = s1668QUnitPartField T b) :
    SectionKPlaceTwoLRootRequired (T := T) (b := b) :=
  ⟨s1677RootCard (l := l) T b h v hv⟩
end LeanFormal.IUT.XiFPaper.S1677UnitKummerActual

end
