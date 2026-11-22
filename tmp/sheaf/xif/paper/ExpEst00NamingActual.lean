import LeanFormal.IUT.IUTIV.Estimates.ElementaryEstimates
import LeanFormal.IUT.IUTIV.Estimates.Section1

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.ExpEst00NamingActual

/-- Naming record for the [ExpEst] (Explicit Estimates in IUT, Kodai 2022) object layer:
reusable tree assets and the naming conventions for the ABC/GenEll consumers. -/
def s3135ExpEstNaming : Audit.Obligation :=
  { id := "EXPEST.00.naming"
    source :=
      "IUT IV section 1 (explicit estimates), IUT IV section 2; tree anchors " ++
        "IUTIV/Estimates/ElementaryEstimates.lean:76-146 (iutIVThm110_e1..e6), " ++
        "IUTIV/Estimates/Section1.lean:23-26 (explicit PNT form, machine-gap), " ++
        "IUTIV/Estimates/Section2.lean:16-19 (Chebyshev/PNT gap notes)"
    status := Audit.VerificationStatus.interface
    note :=
      "NAMING: this stream formalizes the [ExpEst] object layer referenced by IUT.  " ++
        "Namespace convention for GenEll/ExpEst consumers: ExpEst<NN><Name>Actual; " ++
        "reuse-first: tree ElementaryEstimates e1-e6 are PROVED (class A) and are " ++
        "re-exported by ExpEst02; explicit PNT/Chebyshev forms are registered as " ++
        "class B paper inputs (Section1.lean:23-26 notes Mathlib has PNT asymptotics " ++
        "but not the explicit-constant forms).  No new paper input beyond the paper's " ++
        "own explicit estimates; no registry edit (frozen 14041)."
    dependsOn := [ "IUT-IV.estimates", "GENELL.P0" ]
    sorryItems :=
      [ "explicit PNT form (Section1.lean:23-26; class B paper input)",
        "Chebyshev-function explicit bounds used by IUT IV section 2 (class B)" ] }

#check s3135ExpEstNaming
end LeanFormal.IUT.XiFPaper.ExpEst00NamingActual
end
