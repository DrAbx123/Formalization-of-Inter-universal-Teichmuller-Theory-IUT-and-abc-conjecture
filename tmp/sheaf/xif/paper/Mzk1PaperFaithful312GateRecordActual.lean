import tmp.sheaf.xif.paper.Mzk1PaperFaithful312NormedActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312RpNormalizationActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312HqnegActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312FinalActual

/-!
# A732 gate record: paper-faithful 3.12 normalized hqneg route

Assembly chain (all compiled with single-file `lake env lean -o`):
1. `Mzk1PaperFaithful312HqnegActual` — `hqneg_iff_rpVolume_lt_one`;
2. `Mzk1PaperFaithful312RpNormalizationActual` — `hqneg_direct` modulo `RpUnitBallHaarOne`;
3. `Mzk1PaperFaithful312NormedActual` — normalized volume (denominator `fullRegion`),
   `hqneg_norm` UNCONDITIONAL, `final_3_12_normed`;
4. `Mzk1PaperFaithful312FinalActual` — `final_3_12_concrete` (direct route).

Gate lines below are the actual `#print axioms` output of the normalized route.
-/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual.hqneg_norm
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual.final_3_12_normed
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual.rpVolume_rpRegion_lt_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual.hqneg_direct
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual.hqneg_iff_rpVolume_lt_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312FinalActual.final_3_12_concrete
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312FinalActual.final_3_12_concrete'
