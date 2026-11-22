import tmp.sheaf.xif.paper.S2441C9PaperCarrierActual

/-! # S2490: obstruction to carrier-only O^▷/T5 construction

S1979 already has two piloted strips with the same bare SourceFTimesMuPrimeStrip
but different associated pilot objects (paperQPilotDivisor D vs 0).  Hence no
function of the bare carrier alone can construct the O^▷ pilot object; the
missing datum is the literal O^▷ submonoid/pro-generator layer, not a property
of SourceFTimesMuPrimeStrip.  The actual piloted T5 binding of S2441 is kept. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
open LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
open LeanFormal.IUT.IUTIV.Estimates

namespace LeanFormal.IUT.XiFPaper.S2490LiteralOProObstructionActual

/-- The q-pilot piloted strip and the unit-generator piloted strip have the
same bare F-prime-strip with times-mu structure. -/
theorem s2490_same_bare_strip (D : S1895PaperInput) :
    (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip =
      (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip :=
  rfl

/-- No function of the bare SourceFTimesMuPrimeStrip alone can produce both
the q-pilot divisor and the zero pilot object. -/
theorem s2490_no_carrier_only_pilot_object (D : S1895PaperInput) :
    ¬ ∃ F : SourceFTimesMuPrimeStrip PaperV →
          IUTIVArithmeticDivisor (PaperFmod D),
        F (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip =
            paperQPilotDivisor D ∧
        F (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip = 0 := by
  rintro ⟨F, hq, h0⟩
  have hsame :
      (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip =
        (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip := rfl
  have hzero : paperQPilotDivisor D = 0 := by
    calc paperQPilotDivisor D
        = F (paperQPilotPilotedStrip D).toSourceFTimesMuPrimeStrip := hq.symm
      _ = F (paperQPilotUnitGeneratorStrip D).toSourceFTimesMuPrimeStrip := by
            rw [hsame]
      _ = 0 := h0
  have hpos : 0 < IUTIVArithmeticDivisor.deg (F := PaperFmod D)
      (paperQPilotDivisor D) := paperQPilotDivisor_deg_pos D
  rw [hzero] at hpos
  simpa using hpos

/-- The actual piloted T5 binding of S2441 remains the maximal actual carrier
binding; literal O^▷ pro-generators are still missing. -/
theorem s2490_piloted_binding_actual (D : S1895PaperInput) :
    Nonempty (S2441PilotedT5Binding D) :=
  ⟨s2441PilotedT5Binding D⟩

#check s2490_same_bare_strip
#check s2490_no_carrier_only_pilot_object
#check s2490_piloted_binding_actual

end LeanFormal.IUT.XiFPaper.S2490LiteralOProObstructionActual
end
