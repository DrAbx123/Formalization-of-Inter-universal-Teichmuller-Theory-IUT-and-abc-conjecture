import tmp.sheaf.xif.paper.S556QvPhiInputActual
import tmp.sheaf.xif.paper.S474Example32GroupLikeIsoActual
import tmp.sheaf.xif.paper.S491AlignedDivisorMapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]

/-- Minimal package: explicit ramification and valuation data plus the exact
naturality statement; no other S556 data remains. -/
structure S561MinimalPackage where
  ramification : RamificationIndexData (K := K)
  valuation : DvSmallValuationFamily (K := K)
  naturality : S556DivisorNaturalityRequired (K := K) ramification valuation

/-- Build S556 data from the minimal package. -/
noncomputable def s561InputData
    (P : S561MinimalPackage (K := K)) : S556InputDataActual (K := K) where
  ramification := P.ramification
  valuationFamily := P.valuation
  divisor_naturality := P.naturality

/-- The actual Input from the minimal package. -/
noncomputable def s561Input (P : S561MinimalPackage (K := K)) :
    Input (qvPhiRamificationModel (K := K) P.ramification) :=
  s556InputActual (K := K) (s561InputData (K := K) P)

theorem s561Input_rationalFunctions
    (P : S561MinimalPackage (K := K)) :
    (s561Input (K := K) P).rationalFunctions =
      example32RationalFunctionsIso (K := K) := rfl

theorem s561Input_divisor
    (P : S561MinimalPackage (K := K)) :
    (s561Input (K := K) P).divisor =
      fun X => example32DivisorAlignedS491 (K := K) P.valuation X := rfl

/-- The only remaining gap: naturality of the aligned divisor against the
qvPhi ramification pullback. -/
def S561NaturalityGap
    (R : RamificationIndexData (K := K))
    (V : DvSmallValuationFamily (K := K)) : Prop :=
  S556DivisorNaturalityRequired (K := K) R V

end LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual

end
