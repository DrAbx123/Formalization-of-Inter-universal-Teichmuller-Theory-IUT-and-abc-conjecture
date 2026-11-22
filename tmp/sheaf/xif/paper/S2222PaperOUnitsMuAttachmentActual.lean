import tmp.sheaf.xif.paper.S2219PaperOUnitsCarrierActual

/-! # S2222: paper O^×μ attachment and q_v/logKummer gap

Attaches the selected S2219 paper O^×/O^×μ carrier to the S2040 paper
attachment semantics: quotient map, kernel, descended action, compatibility, and
torsion/2l-root triviality in the quotient are actual.  The q_v/logKummer
compatibility datum is recorded as exact missing. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The S2219 carrier has the actual paper O^×μ quotient structure. -/
structure S2222PaperOUnitsMuAttachment
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  quotient_ker :
    MonoidHom.ker (s2219QuotientMap T b) =
      CommGroup.torsion (S2219PaperOUnits T b)
  quotient_surjective :
    Function.Surjective (s2219QuotientMap T b)
  action_compat :
    ∀ (σ : S2147PaperIntegralClosureGaloisGroup T b)
      (u : S2219PaperOUnits T b),
        s2219OUnitsMuAction T b σ (s2219QuotientMap T b u) =
          s2219QuotientMap T b (s2219GaloisAction T b σ u)
  nontrivial_action :
    ∃ (σ : S2147PaperIntegralClosureGaloisGroup T b)
      (u : S2219PaperOUnits T b), s2219GaloisAction T b σ u ≠ u

noncomputable def s2222Attachment :
    S2222PaperOUnitsMuAttachment T b where
  quotient_ker := s2219QuotientMap_ker T b
  quotient_surjective := s2219QuotientMap_surjective T b
  action_compat := s2219OUnitsMuAction_quotientMap T b
  nontrivial_action := s2219NontrivialAction T b

/-- Torsion/root-of-unity indeterminacy is killed by the paper quotient map. -/
theorem s2222_torsion_quotient_trivial
    (u : S2219PaperOUnits T b)
    (hu : u ∈ CommGroup.torsion (S2219PaperOUnits T b)) :
    s2219QuotientMap T b u = 1 := by
  rw [s2219QuotientMap, TimesMuQuotient.quotientMap_apply]
  exact (QuotientGroup.eq_one_iff _).mpr hu

/-- In particular, any 2l-th root of unity has trivial image in the paper O^×μ. -/
theorem s2222_pow_eq_one_quotient_trivial
    (u : S2219PaperOUnits T b) (n : Nat) (hn : 0 < n)
    (hu : u ^ n = 1) :
    s2219QuotientMap T b u = 1 := by
  apply s2222_torsion_quotient_trivial T b
  rw [CommGroup.mem_torsion]
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hu⟩

/-- Exact missing q_v/logKummer compatibility datum on the selected paper O^×μ. -/
structure S2222QVLogKummerRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  qv : S2147PaperIntegralClosure T b
  qv_integral : qv ∈ Integers (S2147PaperIntegralClosure T b)
  qv_norm_lt_one : ‖qv‖ < 1
  logKummer : S2219PaperOUnits T b →* S2219PaperOUnits T b
  logKummer_qv_compatible : Prop

def S2222QVLogKummerRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2222QVLogKummerRequired T b)

#check S2222PaperOUnitsMuAttachment
#check s2222Attachment
#check s2222_torsion_quotient_trivial
#check s2222_pow_eq_one_quotient_trivial
#check S2222QVLogKummerRequired
#check S2222QVLogKummerRequiredProp

end LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual
end
