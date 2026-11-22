import tmp.sheaf.lana_latest.Iut.Multiradial.PrimeStrip.Full
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData

/-! Mainline (A515-1): the Theorem 3.11 prime-strip objects, taken from the real LANA-latest
`Multiradial.PrimeStrip.Full` module (IUT I, Definitions 4.1 and 5.2 prime-strips with
their isomorphisms, tautological strips, `F ↦ D` maps), together with the bookkeeping link
to Gogopex's `QualitativeData` identifiers (IPL/SHE/APT names).  No large file is copied:
all objects and proofs are the LANA declarations, re-exported under our namespace. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311PrimeStripActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! ## 1. The prime-strip objects (LANA real declarations) -/

section PrimeStrips

variable (D : Iut.InitialThetaData.{0})

/-- Theorem 3.11 prime-strip object `D` (IUT I, Definition 4.1(i)). -/
abbrev Thm311DStrip : Type 1 := Iut.Multiradial.PrimeStrip.DStrip D

/-- The mono-analytic `D^⊢`-prime-strip (IUT I, Definition 4.1(iii)). -/
abbrev Thm311DVdashStrip : Type 1 := Iut.Multiradial.PrimeStrip.DVdashStrip D

/-- The Frobenius-like `F`-prime-strip (IUT I, Definition 5.2(i)). -/
abbrev Thm311FStrip : Type 1 := Iut.Multiradial.PrimeStrip.FStrip D

/-- The mono-analytic `F^⊢`-prime-strip (IUT I, Definition 5.2(ii)). -/
abbrev Thm311FVdashStrip : Type 1 := Iut.Multiradial.PrimeStrip.FVdashStrip D

/-- The `F^{⊢×μ}`-prime-strip of the Θ-link (IUT II, Definition 4.9(v)). -/
abbrev Thm311FMuStrip : Type 1 := Iut.Multiradial.PrimeStrip.FMuStrip D

/-- The tautological `D`-prime-strip of initial Θ-data (IUT I, Example 4.3(iv)). -/
def thm311DStripOfThetaData : Thm311DStrip D :=
  Iut.Multiradial.PrimeStrip.DStrip.ofThetaData D

/-- The tautological `F`-prime-strip of initial Θ-data (IUT I, Example 4.3(iv)). -/
def thm311FStripOfThetaData : Thm311FStrip D :=
  Iut.Multiradial.PrimeStrip.FStrip.ofThetaData D

/-- The tautological `F^{⊢×μ}`-strip (used by the Θ-link of the Hodge theater). -/
def thm311FMuStripOfThetaData : Thm311FMuStrip D :=
  Iut.Multiradial.PrimeStrip.FMuStrip.ofThetaData D

/-- The forgetful map `F ↦ D` on prime-strips (IUT I, Remark 5.2.1(i)). -/
def thm311FStripToD (P : Thm311FStrip D) : Thm311DStrip D :=
  Iut.Multiradial.PrimeStrip.FStrip.toD P

/-- The forgetful map `F^⊢ ↦ D^⊢` (IUT I, Remark 5.2.1(i)). -/
def thm311FVdashStripToD (P : Thm311FVdashStrip D) : Thm311DVdashStrip D :=
  Iut.Multiradial.PrimeStrip.FVdashStrip.toD P

/-- Any two `D`-prime-strips are isomorphic (LANA real theorem). -/
theorem thm311DStrip_nonempty_iso (P Q : Thm311DStrip D) :
    Nonempty (P.Iso Q) :=
  Iut.Multiradial.PrimeStrip.DStrip.nonempty_iso P Q

/-- Any two `F`-prime-strips are isomorphic (LANA real theorem). -/
theorem thm311FStrip_nonempty_iso (P Q : Thm311FStrip D) :
    Nonempty (P.Iso Q) :=
  Iut.Multiradial.PrimeStrip.FStrip.nonempty_iso P Q

/-- Any two `F^{⊢×μ}`-strips are isomorphic (LANA real theorem). -/
theorem thm311FMuStrip_nonempty_iso (P Q : Thm311FMuStrip D) :
    Nonempty (P.Iso Q) :=
  Iut.Multiradial.PrimeStrip.FMuStrip.nonempty_iso P Q

/-- The forgetful map on `F`-prime-strip isomorphisms. -/
theorem thm311FStrip_isoToD {P Q : Thm311FStrip D} (f : P.Iso Q) :
    (thm311FStripToD D P).Iso (thm311FStripToD D Q) :=
  Iut.Multiradial.PrimeStrip.FStrip.isoToD f

end PrimeStrips

/-! ## 2. Bookkeeping link to Gogopex `QualitativeData` -/

open Iut.RealLineCopy.QualitativeData

/-- The bookkeeping identifier of the `D`-prime-strip. -/
def dStripQualitativeId : PrimeStripId := ⟨"D-prime-strip"⟩

/-- The bookkeeping identifier of the `F`-prime-strip. -/
def fStripQualitativeId : PrimeStripId := ⟨"F-prime-strip"⟩

/-- The bookkeeping identifier of the `F^{⊢×μ}`-prime-strip. -/
def fMuStripQualitativeId : PrimeStripId := ⟨"F^⊢×μ-prime-strip"⟩

/-- The bookkeeping IPL link from the `F`-strip to the `D`-strip (names only; the
  mathematical link is the real `F ↦ D` map above). -/
def fToDQualitativeLink : PrimeStripLink where
  source := fStripQualitativeId
  target := dStripQualitativeId
  linkLabel := "F ↦ D (IUT I, Remark 5.2.1(i))"

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311PrimeStripActual