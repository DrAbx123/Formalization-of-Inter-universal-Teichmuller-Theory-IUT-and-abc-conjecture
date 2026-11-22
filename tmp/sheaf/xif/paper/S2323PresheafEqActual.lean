import tmp.sheaf.xif.paper.S2322NatIsoDirectActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2322NatIsoDirectActual
open LeanFormal.IUT.XiFPaper.S2312EqualizerIsoFinal2Actual
open LeanFormal.IUT.XiFPaper.S2308EqualizerIsoFinalActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2323PresheafEqActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
variable (T : (Over S)ᵒᵖ)

-- Proposed equality route:
--   (Limits.equalizer (S2285f S M) (S2285g S N)).obj T
--     = {g : SignGroup // g • S2267PT S M T = S2267QT S N T}
-- is NOT obtainable from the existing data in Lean without univalence.
-- We have:
--   S2312EqualizerSubtypeIso : equalizer.obj T ≅ subtype
--   S2271QHomObj_eq_subtype : Q.obj T = subtype
-- An Iso does not yield a type equality; eqToIso requires an equality, not an
-- Iso.  The only available equality is for Q.obj T, not for the functor-category
-- equalizer object.  Hence the presheaf-level equality route is blocked unless
-- the equalizer object is redefined to be the subtype pointwise.
#check S2312EqualizerSubtypeIso
#check S2312QHomEqualizerObjIso
#check S2271QHomObj_eq_subtype
#check S2322Comp

end LeanFormal.IUT.XiFPaper.S2323PresheafEqActual

end
