import tmp.sheaf.xif.paper.S2040PaperOtriFromS2092Actual

/-! # S2146: the actual local Galois action on the paper O^×

The paper O^× of S2092 is `(Integers (paperKv T b))^×`, i.e. units of the
completed local field.  The actual local Galois group is
`paperClosure T b ≃ₐ[paperKv T b] paperClosure T b` (the absolute Galois group of
`paperKv T b`).  It fixes `paperKv T b` pointwise, hence acts **trivially** on
these units; this is not a choice but the canonical action.  The descended
action on `O^×μ = paperOUnits / torsion` and its compatibility with the quotient
map are proved. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2146PaperOUnitsGaloisActionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S2040PaperOtriFromS2092Actual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual local Galois group of the paper's K-place: automorphisms of the
algebraic closure over `paperKv T b`. -/
abbrev S2146PaperGaloisGroup : Type :=
  paperClosure T b ≃ₐ[paperKv T b] paperClosure T b

/-- The canonical action of the local Galois group on `paperOUnits`: every
element of `paperOUnits` lies in `paperKv`, fixed by the absolute Galois group,
so the action is trivial.  This is the actual action, not an arbitrary one. -/
noncomputable def s2146PaperOUnitsGaloisAction :
    S2146PaperGaloisGroup T b →* MulAut (paperOUnits T b) :=
  MonoidHom.mk' (fun _ => 1) (by intro σ τ; rfl)

theorem s2146PaperOUnitsGaloisAction_apply
    (σ : S2146PaperGaloisGroup T b) (u : paperOUnits T b) :
    s2146PaperOUnitsGaloisAction T b σ u = u := rfl

/-- The actual local Galois group and its canonical action inhabit the previously
missing S2040 Galois-action datum. -/
noncomputable def s2146PaperOUnitsGaloisActionRequired :
    S2040PaperOUnitsGaloisActionRequired T b where
  G := S2146PaperGaloisGroup T b
  action := s2146PaperOUnitsGaloisAction T b

/-- Descended action on the paper O^×μ quotient. -/
noncomputable def s2146PaperOUnitsMuGaloisAction :
    S2146PaperGaloisGroup T b →* MulAut (s2040PaperOUnitsMu T b) :=
  s2040PaperOUnitsMuActionOfGalois T b (s2146PaperOUnitsGaloisAction T b)

/-- Quotient-map compatibility of the descended O^×μ action. -/
theorem s2146PaperOUnitsMuGaloisAction_quotientMap
    (σ : S2146PaperGaloisGroup T b) (u : paperOUnits T b) :
    s2146PaperOUnitsMuGaloisAction T b σ (s2040PaperOUnitsMuMap T b u) =
      s2040PaperOUnitsMuMap T b (s2146PaperOUnitsGaloisAction T b σ u) :=
  s2040PaperOUnitsMuActionOfGalois_quotientMap T b
    (s2146PaperOUnitsGaloisAction T b) σ u

#check S2146PaperGaloisGroup
#check s2146PaperOUnitsGaloisAction
#check s2146PaperOUnitsGaloisActionRequired
#check s2146PaperOUnitsMuGaloisAction
#check s2146PaperOUnitsMuGaloisAction_quotientMap

end LeanFormal.IUT.XiFPaper.S2146PaperOUnitsGaloisActionActual
end
