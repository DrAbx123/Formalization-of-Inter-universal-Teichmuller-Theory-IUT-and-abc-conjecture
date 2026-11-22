/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HqnegHullModelActual
import tmp.sheaf.xif.paper.Mzk1Cor312RequirementResolvedActual

/-!
# A597/A598: Cor 3.12 with `hqneg` DISCHARGED on the concrete hull model

The sign hypothesis of the final 3.12 statement is discharged by the concrete
hull-side model of `Mzk1HqnegHullModelActual`:
* `canonicalReading (T := T) (qRead := qRead) hq`, `canonicalHqneg hq` are constructed there for any
  strictly negative q-pilot log-volume `qRead`;
* here `cor312_hqneg_discharged` uses `cor312Conclusion_final` with that reading and
  the PROVED `canonicalHqneg`, so no sign hypothesis remains;
* the only remaining parameters are the abstract evidence props `ipl/she/apt` and
  their real proofs (they are parameters, not axioms/placeholders).

No object is changed; no `sorry`/custom axiom.  ABC gate NOT passed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312HqnegDischargedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **Cor 3.12 with `hqneg` discharged**: for any strictly negative q-pilot
  log-volume `qRead`, the concrete model's canonical reading satisfies the sign
  hypothesis by proof, and only the abstract evidence parameters remain. -/
theorem cor312_hqneg_discharged {qRead : ℝ} (hq : qRead < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T (canonicalReading (T := T) (qRead := qRead) hq) (canonicalHqneg (T := T) (qRead := qRead) hq)
        ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T (canonicalReading (T := T) (qRead := qRead) hq) (canonicalHqneg (T := T) (qRead := qRead) hq)
    ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1Cor312HqnegDischargedActual

/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged

end