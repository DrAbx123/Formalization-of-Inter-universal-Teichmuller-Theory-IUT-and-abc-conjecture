/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.IPLAPTActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import tmp.sheaf.xif.paper.Mzk1N8IplSheAptStatementActual
import tmp.sheaf.xif.paper.Mzk1IPLFamilyV2Actual

/-! A516: IPL/APT/SHE object composition for the 3.12 route: an actual
IPLActual (Remark 3.11.1(iii)) together with the N8 IPL/SHE/APT compatibility
statement, plus the concrete self-IPL instance from IPLAPTDataActual. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1IPLAPTCompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.Mzk1N8IplSheAptStatementActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

universe uV uG

variable {V : Type uV}

/-- The IPL/APT/SHE object: an actual IPL link factorization plus the
compatibility statement for the three operations. -/
structure IPLAPTComposition {G : Type uG} [Group G] [TopologicalSpace G]
    (intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V)
    (apt she ipl : Prop) where
  iplData : IPLActual (G := G) intermediateStrip gauStrip envStrip coricEnvStrip
    qPilotStrip
  aptCompatibility : APTCompatibility apt
  sheCompatibility : SHECompatibility she
  iplCompatibility : IPLCompatibility ipl

namespace IPLAPTComposition

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
variable {apt she ipl : Prop}
variable (C : IPLAPTComposition (V := V) (G := G) intermediateStrip gauStrip
  envStrip coricEnvStrip qPilotStrip apt she ipl)

/-- The actual IPL input link is the frozen Kummer/evaluation composite. -/
theorem ipl_inputLink_eq_composite :
    C.iplData.inputLink = C.iplData.composite :=
  IPLActual.inputLink_eq_composite C.iplData

/-- The IPL data packages as the frozen SourceLinkFactorization record. -/
def ipl_linkFactorization :
    SourceLinkFactorization G intermediateStrip gauStrip envStrip coricEnvStrip
      qPilotStrip :=
  IPLActual.toLinkFactorization C.iplData

/-- The compatibility bundle statement. -/
def statement : N8IplSheAptStatement apt she ipl :=
  ⟨C.aptCompatibility, C.sheCompatibility, C.iplCompatibility⟩

/-- APT compatibility projection. -/
theorem apt_compatibility : APTCompatibility apt := C.aptCompatibility

/-- SHE compatibility projection. -/
theorem she_compatibility : SHECompatibility she := C.sheCompatibility

/-- IPL compatibility projection. -/
theorem ipl_compatibility : IPLCompatibility ipl := C.iplCompatibility

end IPLAPTComposition

/-! ## The concrete self-IPL composition -/

/-- The concrete self-IPLAPT composition on the canonical strip: the actual
self IPLActual from IPLAPTDataActual, with the N8 statement discharged by the
trivial compatibility proofs. -/
noncomputable def selfComposition (envStrip : FPrimeStrip V) :
    IPLAPTComposition (V := V) (G := SelfGroup envStrip)
      envStrip envStrip envStrip envStrip envStrip True True True where
  iplData := selfIplActual envStrip
  aptCompatibility := trivial
  sheCompatibility := trivial
  iplCompatibility := trivial

theorem selfComposition_constructed (envStrip : FPrimeStrip V) :
    (selfComposition envStrip).iplData = selfIplActual envStrip := rfl

/-- The self-IPL factorization is definitional on the constructed data. -/
theorem selfComposition_factorization (envStrip : FPrimeStrip V) :
    (selfComposition envStrip).iplData.inputLink =
      (selfComposition envStrip).iplData.composite :=
  IPLActual.inputLink_eq_composite (selfComposition envStrip).iplData

end LeanFormal.IUT.XiFPaper.Mzk1IPLAPTCompositionActual
