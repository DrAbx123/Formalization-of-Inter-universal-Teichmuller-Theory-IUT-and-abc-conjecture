import tmp.sheaf.xif.paper.S432SmallModelActual
import tmp.sheaf.xif.paper.S433Example32RationalDivisorActual
import tmp.sheaf.xif.paper.S442DvCoverNormPullbackActual

/-!
# S445: conditional Example32SmallInput from S433/S442 data

`Example32SmallInputData` packages the global q_v valuation family, the
per-cover rational-function group, the divisor map built from the S433
normalized divisor coefficient, its naturality, and the S442 norm
compatibility.  These are explicit parameters: existence is not asserted.
From such data we construct the actual `Input` for `example32Phi` and then
the conditional FrobenioidPresentation of S432.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S445Example32SmallInputActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S433Example32RationalDivisorActual
open LeanFormal.IUT.XiFPaper.S442DvCoverNormPullbackActual
open Iut.SourceModelFrobenioid

universe u

variable (K : Type u) [Field K]

/-- Explicit conditional data for the Example 3.2 model Input.  The global
valuation family and norm compatibility are carried as hypotheses; no
existence or construction is asserted for them. -/
structure Example32SmallInputData where
  valuationFamily : Prop
  normCompatibility : Prop
  rationalFunctions :
    GroupLikeAddMonoidOn (Example32SmallBase K) (fun {_ _} _ => True)
  divisor :
    ∀ X : Example32SmallBase K,
      rationalFunctions.obj X →+
        Algebra.GrothendieckAddGroup ((example32Phi K).obj X).carrier
  divisor_naturality :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : rationalFunctions.obj Y),
      divisor X (rationalFunctions.pullback f value) =
        (example32Phi K).gpPullback f (divisor Y value)

/-- Conditional actual Input constructed from the explicit data. -/
noncomputable def example32SmallInputOfData
    (D : Example32SmallInputData K) : Example32SmallInput K where
  rationalFunctions := D.rationalFunctions
  divisor := D.divisor
  divisor_natural := D.divisor_naturality

/-- Conditional actual FrobenioidPresentation from the Input data, connectedness
and total-epimorphicity hypotheses. -/
noncomputable def example32SmallFrobenioidPresentationOfData
    (D : Example32SmallInputData K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  example32SmallFrobenioidPresentation (K := K)
    (example32SmallInputOfData K D) baseTotallyEpimorphic

end LeanFormal.IUT.XiFPaper.S445Example32SmallInputActual
end
