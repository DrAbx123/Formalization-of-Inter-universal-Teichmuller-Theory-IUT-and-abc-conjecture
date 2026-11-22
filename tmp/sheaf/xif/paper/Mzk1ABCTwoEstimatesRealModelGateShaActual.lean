import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesRealModelShaActual

/-!
# shehdd A612 real-model gate (log-only, Sha)

`#print axioms` for the real-model conditional bridge:
* `abc_of_realGap1Gap2` (Gap 1 height + Gap 2 volume ⇒ ABCConjecture);
* `heightBound_of_realGap1Gap2`.
Expected only `[propext, Classical.choice, Quot.sound]`; Gap-1/Gap-2 are explicit
hypotheses, not axioms.  This gate verifies the honest real-model wiring, with
NO `logVolume := arithmeticWeight` substitution.
-/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelShaActual.abc_of_realGap1Gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelShaActual.heightBound_of_realGap1Gap2
