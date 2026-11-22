import tmp.sheaf.xif.paper.S1312D7LocalGroupActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import tmp.sheaf.xif.paper.S1331OrbicurveClauseAudit

/-! # S1386: D7b curve-side local group prefix

S1312 identifies the exact D7b first field:
  (S1312D7Layer l).valuationCarrier -> Type.
This file records the actual prefix projection from any D7b supply and the
curve-side global donors present in S1348/S1319/S1331.

What is NOT constructed: a place-indexed family of geometric local groups
Pi_Xv / Pi_Cv and the map Pi_Xv -> Pi_Cv.  S1348 supplies a global disconnected
K-point cover and its structure group; S1319/S1331 supply global arithmetic
l-torsion/exact-sequence data, not local curve groups.  The arithmetic G_v is
not used.  No inhabitant of the D7b supply is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1386D7bLocalGroupActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1312D7LocalGroupActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit

/-- D7a layer on the S1280 arithmetic input. -/
abbrev S1386Layer (l : PrimeGeFive) : SourceValuationSectionLayer (S1280Arithmetic l) :=
  S1312D7Layer l

/-- The exact D7b first field: place-indexed local-group carrier. -/
abbrev S1386D7bFirstField (l : PrimeGeFive) : Type 1 :=
  (S1386Layer l).valuationCarrier → Type

/-- The exact D7b prefix: two place-indexed group carriers and the pointwise
section equivalence.  This is the curve-side Pi_Xv/Pi_Cv shape; it is not the
arithmetic G_v and it is not yet constructed. -/
structure S1386CurveLocalGroupPrefix (l : PrimeGeFive) where
  localGroupCarrier : (S1386Layer l).valuationCarrier → Type
  modifiedLocalGroupCarrier : (S1386Layer l).modifiedValuationCarrier → Type
  localGroupSection : ∀ x, localGroupCarrier x →
    modifiedLocalGroupCarrier ((S1386Layer l).sectionMap x)
  localGroupSection_injective : ∀ x, Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x, Function.Surjective (localGroupSection x)

/-- Actual projection: every D7b supply contains this prefix. -/
noncomputable def S1386CurveLocalGroupPrefixOfSupply
    (l : PrimeGeFive) (G : S1312D7bRequirement l) :
    S1386CurveLocalGroupPrefix l where
  localGroupCarrier := G.localGroupCarrier
  modifiedLocalGroupCarrier := G.modifiedLocalGroupCarrier
  localGroupSection := G.localGroupSection
  localGroupSection_injective := G.localGroupSection_injective
  localGroupSection_surjective := G.localGroupSection_surjective

/-- Global curve-side donor data available in S1348/S1319/S1331.  This is only
a global tuple; it is not a place-indexed local-group family. -/
abbrev S1386GlobalCurveDonors (l : PrimeGeFive) : Type 1 :=
  S1348Cover l × S1348StructureGroup l × S1331ExactSequenceResidual l

#check S1386D7bFirstField
#check S1386CurveLocalGroupPrefix
#check S1386CurveLocalGroupPrefixOfSupply
#check S1386GlobalCurveDonors

end LeanFormal.IUT.XiFPaper.S1386D7bLocalGroupActual
end