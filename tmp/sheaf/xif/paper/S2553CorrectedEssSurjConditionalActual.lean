import tmp.sheaf.xif.paper.S2541EssSurjAuditActual
import tmp.sheaf.xif.paper.S2519InvEquivalenceGoalActual
import tmp.sheaf.xif.paper.S2547TransportIsoActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2553CorrectedEssSurjConditionalActual

/-- The corrected representable essential-surjectivity target. -/
def S2553CorrectedEssSurj : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
    S2541Representable X →
      ∃ C : FiniteEtaleCover S2482AffineScheme,
        Nonempty (S2517InvObj C ≅ X)

/-- The exact roundtrip still needed for the canonical preimage cover. -/
def S2553PreimageRoundtrip : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
    S2541Representable X →
      Nonempty (S2517InvObj (S2519PreimageCover X) ≅ X)

theorem S2553CorrectedEssSurj_of_roundtrip
    (h : S2553PreimageRoundtrip) :
    S2553CorrectedEssSurj := by
  intro X hX
  exact ⟨S2519PreimageCover X, h X hX⟩

#check S2553CorrectedEssSurj
#check S2553PreimageRoundtrip
#check S2553CorrectedEssSurj_of_roundtrip
#print axioms S2553CorrectedEssSurj_of_roundtrip
end LeanFormal.IUT.XiFPaper.S2553CorrectedEssSurjConditionalActual
end