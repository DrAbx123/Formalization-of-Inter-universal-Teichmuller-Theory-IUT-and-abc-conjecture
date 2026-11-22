import tmp.sheaf.xif.paper.S2183QHomEqualizerIdActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2183QHomEqualizerIdActual
open LeanFormal.IUT.XiFPaper.S2181EqualizerSheafActual
open LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual
open LeanFormal.IUT.XiFPaper.S2160QHomSheafActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2191QHomEqualizerIdActual

/-- The exact first missing for the Q hom-presheaf equalizer identification:
for every S,M,N, construct the constant sign group sheaf P, the representable
morphism sheaf R, the two natural transformations f,g, and the isomorphism
S2152Q.presheafHom M N ≅ Limits.equalizer f g. -/
def S2191QHomEqualizerIdentification : Prop :=
  S2168QHomEqualizerIdentification

/-- The first missing is exactly the S2168 identification. -/
theorem S2191QHomEqualizerIdentification_iff :
    S2191QHomEqualizerIdentification ↔
      S2168QHomEqualizerIdentification :=
  Iff.rfl

/-- Conditional actual: identification plus the proved S2181 equalizer sheaf
lemma gives the Q hom-presheaf sheaf condition. -/
theorem S2191QHomSheafFor_of_identification
    (h : S2191QHomEqualizerIdentification) :
    S2160QHomSheafFor :=
  S2183QHomSheafFor_of_identification h

/-- Present exact first missing. -/
def S2191FirstMissing : Prop := S2191QHomEqualizerIdentification

#print axioms S2191QHomEqualizerIdentification_iff
#print axioms S2191QHomSheafFor_of_identification

end LeanFormal.IUT.XiFPaper.S2191QHomEqualizerIdActual

end
