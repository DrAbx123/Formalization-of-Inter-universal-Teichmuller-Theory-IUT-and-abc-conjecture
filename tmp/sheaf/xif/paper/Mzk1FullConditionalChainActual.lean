/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C1DonorConditionalActual
import tmp.sheaf.xif.paper.Mzk1LGenericConditionalActual
import Mathlib.Tactic

/-! # A968: merged conditional chain (C1 donor hypotheses + C3L data) -/

/-
CONDITIONAL on (a) the C1 donor five-field hypotheses `NativeC1DonorHypotheses` and
(b) the explicit C3L data assumption `SourcePilotRegionLGeneric`.  NOT an unconditional
construction.  The C1/C2 witnesses are obtained from the A963 conditional chain
(`packetOfHypotheses`, `sourceInputBinding_nonempty_ofHypotheses`,
`sourceLogKummerData_nonempty_ofHypotheses`); C3L is the class-B explicit data; the merged
result is `Nonempty (QPilotLineActualLGeneric I)` with `I = (packetOfHypotheses H).input`.
No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FullConditionalChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1LGenericConditionalActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization

variable {l : PrimeGeFive}

/-- C1 witness from the donor hypotheses (the packet's source input binding). -/
noncomputable def c1OfDonor (H : NativeC1DonorHypotheses (l := l)) :
    SourceInputBinding (packetOfHypotheses H).input :=
  (packetOfHypotheses H).sourceInputBinding

/-- C2 witness from the donor hypotheses (chosen from the proved nonemptiness). -/
noncomputable def c2OfDonor (H : NativeC1DonorHypotheses (l := l)) :
    SourceLogKummerData (packetOfHypotheses H).input (c1OfDonor H) :=
  Classical.choice (sourceLogKummerData_nonempty_ofHypotheses H)

/-- C1+C2 core from the donor hypotheses. -/
noncomputable def genericCoreOfDonor (H : NativeC1DonorHypotheses (l := l)) :
    QPilotLineGenericCore (l := l) (packetOfHypotheses H).input where
  C1 := c1OfDonor H
  C2 := c2OfDonor H

/-- **Merged full chain**: donor hypotheses plus C3L data give the generic q-pilot line. -/
theorem fullChain (H : NativeC1DonorHypotheses (l := l))
    (C3L : SourcePilotRegionLGeneric (l := l) (packetOfHypotheses H).input) :
    Nonempty (QPilotLineActualLGeneric (l := l) (packetOfHypotheses H).input) :=
  ⟨{ C1 := c1OfDonor H, C2 := c2OfDonor H, C3L := C3L }⟩

/-- The same chain through `LGenericAssumptions`. -/
theorem fullChain_via_assumptions (H : NativeC1DonorHypotheses (l := l))
    (C3L : SourcePilotRegionLGeneric (l := l) (packetOfHypotheses H).input) :
    Nonempty (QPilotLineActualLGeneric (l := l) (packetOfHypotheses H).input) :=
  qPilotLineActualLGeneric_nonempty_of_assumptions
    { C1 := c1OfDonor H, C2 := c2OfDonor H, C3L := C3L }

def fullChainRows : List (String × String) :=
  [ ("NativeC1DonorHypotheses", "(a) five donor fields") ,
    ("c1OfDonor", "C1 SourceInputBinding from packet") ,
    ("c2OfDonor", "C2 SourceLogKummerData (choice)") ,
    ("genericCoreOfDonor", "QPilotLineGenericCore") ,
    ("SourcePilotRegionLGeneric", "(b) class-B C3L explicit data") ,
    ("fullChain / fullChain_via_assumptions", "merged Nonempty chain (PROVED)") ]

theorem fullChainRows_length : fullChainRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1FullConditionalChainActual
