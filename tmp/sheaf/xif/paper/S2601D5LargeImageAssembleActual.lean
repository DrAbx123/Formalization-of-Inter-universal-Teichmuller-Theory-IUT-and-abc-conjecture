/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2600D5FinalResidueActual
import tmp.sheaf.xif.paper.S2676RangeCycleType1249Actual
import tmp.sheaf.xif.paper.S2619DetSurjectiveOfTwelveCycleActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2001D5LargeImageSubstepsActual

/-!
# S2601: assembly of the D5 range hypotheses at the actual basis

This file assembles the three fields of `S2057RangeHypothesesData` at the
actual rank-two basis `S1982Basis` from the unconditional arithmetic inputs:

* determinant surjectivity: `S2619DetSurjective_of_twelveCycleInput` applied
  to the unconditional twelve-cycle input `S2600_twelveCycleInput` of S2600;
* pair transitivity: `S2440RangePairTransitive_of_twelveCycle` applied to the
  same twelve-cycle input;
* cycle type `(10, 2)`: the unconditional `S2676_rangeCycleType102` of S2676.

The resulting data is fed to both assembly theorems:

* `S2601_d5LargeImage : S1987D5LargeImageFive` from
  `s2057Target_of_rangeHypotheses` (S2057);
* `S2601_target_via_S2001 : S1987D5LargeImageFive` from
  `S2001Target_of_rangeHypotheses` (S2001).

No sorry, axiom, native_decide or True is used: every declaration below is an
actual Lean object, and all inputs are theorems of the imported files.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2601D5LargeImageAssembleActual

open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2600D5FinalResidueActual
open LeanFormal.IUT.XiFPaper.S2619DetSurjectiveOfTwelveCycleActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2676RangeCycleType1249Actual
open LeanFormal.IUT.XiFPaper.S2001D5LargeImageSubstepsActual

/-- The S2057 range-hypothesis data at the actual basis `S1982Basis`,
assembled from the unconditional determinant, pair-transitivity and
cycle-type inputs. -/
noncomputable def S2601RangeHypothesesData :
    S2057RangeHypothesesData S1982Basis where
  det_surjective :=
    S2619DetSurjective_of_twelveCycleInput S2600_twelveCycleInput
  pair_transitive :=
    S2440RangePairTransitive_of_twelveCycle S2600_twelveCycleInput
  cycle_type_102 := S2676_rangeCycleType102

/-- **The S1987 D5 large-image target**, obtained by applying the S2057
assembly theorem to the range-hypothesis data at `S1982Basis`. -/
theorem S2601_d5LargeImage : S1987D5LargeImageFive :=
  s2057Target_of_rangeHypotheses S1982Basis S2601RangeHypothesesData

/-- The same target obtained through the S2001 assembly theorem. -/
theorem S2601_target_via_S2001 : S1987D5LargeImageFive :=
  S2001Target_of_rangeHypotheses S1982Basis S2601RangeHypothesesData

#check S2601RangeHypothesesData
#check S2601_d5LargeImage
#check S2601_target_via_S2001
#print axioms S2601RangeHypothesesData
#print axioms S2601_d5LargeImage
#print axioms S2601_target_via_S2001

end LeanFormal.IUT.XiFPaper.S2601D5LargeImageAssembleActual
end
