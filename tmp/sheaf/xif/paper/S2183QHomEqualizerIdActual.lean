import tmp.sheaf.xif.paper.S2181EqualizerSheafActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2181EqualizerSheafActual
open LeanFormal.IUT.XiFPaper.S2168QHomSheafEqualizerActual
open LeanFormal.IUT.XiFPaper.S2160QHomSheafActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2183QHomEqualizerIdActual

/-- The remaining exact first missing for the Q hom-presheaf: for every S,M,N,
construct the equalizer sheaves P,R, maps f,g and the isomorphism with
S2152Q.presheafHom M N. -/
def S2183QHomEqualizerIdentification : Prop :=
  S2168QHomEqualizerIdentification

/-- The first missing is exactly the S2168 equalizer identification. -/
theorem S2183QHomEqualizerIdentification_iff :
    S2183QHomEqualizerIdentification ↔
      S2168QHomEqualizerIdentification :=
  Iff.rfl

/-- Conditional actual: equalizer identification gives the Q hom-presheaf
sheaf condition, using the proved S2181 equalizer sheaf lemma. -/
theorem S2183QHomSheafFor_of_identification
    (h : S2183QHomEqualizerIdentification) :
    S2160QHomSheafFor :=
  S2181QHomSheafFor_of_identification h

/-- The exact first missing in the present package. -/
def S2183FirstMissing : Prop := S2183QHomEqualizerIdentification

/-! ## Required data (documentation boundary)

The intended equalizer data for fixed S,M,N is:

- P : (Over S)ᵒᵖ ⥤ Type, the constant sign group sheaf;
- R : (Over S)ᵒᵖ ⥤ Type, the representable morphism sheaf into S1726AffineOver;
- f g : P ⟶ R, encoding g |-> g . P_T and g |-> Q_T;
- iso : S2152Q.presheafHom M N ≅ Limits.equalizer f g.

No such data is constructed in this file. -/

#print axioms S2183QHomEqualizerIdentification_iff
#print axioms S2183QHomSheafFor_of_identification

end LeanFormal.IUT.XiFPaper.S2183QHomEqualizerIdActual

end
