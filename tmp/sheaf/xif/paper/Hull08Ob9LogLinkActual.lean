import tmp.sheaf.xif.paper.Indet05RouteMultiradialClassActual
import tmp.sheaf.xif.paper.S3182Cor312HullDetAssemblyActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: Ob9|log-link compatibility|indeterminacy|Ind1|Ind2|Ind3|multiradial up-to -> hits Indet05RouteMultiradialClassActual:40-113 (routeMultiradial_ind1/ind2/ind3_logVolume_le/ind3_level/ind3_possibleImage_upper, RouteMultiradialUpTo/repClass/repClass_congr), Indet01/Indet02 (A35 first-triangle layer), S3139SourceMultiradialQuotientActual (descended multiradial map) -> REUSE (route-side Ob9/log-link indeterminacy layer; class-level invariance only).

# [Hull] 08: H7 (Ob9) log-link compatibility at the route multiradial class

Corpus: IUT III Remark 3.9.4 (corpus ~7151: log-link compatibility as elementary
observations); Remark 3.9.5; Step (xi) corpus 10750-10987; Cor 3.12 statement
corpus 10324-10353; conclusion 10897; Indet05 anchors (IUT III 653-679).
CONTENT: hull-side H7/Ob9 consumer.  The route multiradial layer already proves:
(Ind1)/(Ind2) act trivially on the descended multiradial map, and (Ind3) is
one-sided (log-volume monotone, level increases by n, possible-image upper-semi),
so the invariant object is the QUOTIENT CLASS.  This file wires that with the
hull+det assembly: from HullDetAssemblyInputs plus a RouteMultiradialUpTo
representative it gets the Cor 3.12 hull+det conclusion AND the three route
indeterminacy laws at the chosen representative.  HONESTY: the deep statement
that ARBITRARY log-link iterates do not affect the comparison is class-B named
(not formalized); only the class-level/one-sided route laws are class A here.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull08Ob9LogLinkActual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}

variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- H7/Ob9 hull-side inputs: the hull+det assembly inputs plus a route multiradial
representative (the invariant object is its quotient class). -/
structure HullOb9Inputs (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  hull : HullDetAssemblyInputs M
  rep : RouteMultiradialUpTo I

/-- **H7/Ob9 route-side consumer (class A):** from the hull+det assembly inputs and
a route multiradial representative, get the Cor 3.12 hull+det conclusion AND the
route (Ind1)/(Ind2) invariance AND the (Ind3) one-sided log-volume law at the
representative.  Every input field is consumed. -/
theorem hull_ob9_interface
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullOb9Inputs (l := l) M I)
    (g : SourceStepXILabel) (n : Nat) :
    Cor312HullDetConclusion M In.hull.theta ∧
      sourceMultiradialMap I ((sourceStepXICore I).ind1 g In.rep.representative) =
        sourceMultiradialMap I In.rep.representative ∧
      sourceMultiradialMap I ((sourceStepXICore I).ind2 g In.rep.representative) =
        sourceMultiradialMap I In.rep.representative ∧
      sourceMultiradialLogVolume I
          (sourceMultiradialMap I In.rep.representative) ≤
        sourceMultiradialLogVolume I
          (sourceMultiradialMap I ((sourceStepXICore I).ind3 n In.rep.representative)) :=
  ⟨cor312_hullDet_conditional M In.hull,
   routeMultiradial_ind1 I g In.rep.representative,
   routeMultiradial_ind2 I g In.rep.representative,
   routeMultiradial_ind3_logVolume_le I n In.rep.representative⟩

/-- The route multiradial up-to class is independent of the (Ind1)/(Ind2)
representative (class A; reused). -/
theorem hull_ob9_repClass_congr
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (x y : RouteMultiradialUpTo I)
    (h : sourceMultiradialMap I x.representative =
      sourceMultiradialMap I y.representative) :
    x.repClass = y.repClass :=
  RouteMultiradialUpTo.repClass_congr x y h

/-- H7/Ob9 classification rows (class A proved vs class B named). -/
def hullOb9Rows : List (String × String × String) :=
  [ ("(Ind1)/(Ind2) invariance of the descended multiradial map", "A", "reused Indet05.routeMultiradial_ind1/ind2 (PROVED)")
  , ("(Ind3) one-sided log-volume monotonicity", "A", "reused Indet05.routeMultiradial_ind3_logVolume_le (PROVED)")
  , ("(Ind3) level increase and possible-image upper-semi", "A", "reused Indet05.routeMultiradial_ind3_level/possibleImage_upper (PROVED)")
  , ("invariant object = quotient class (up-to)", "A", "reused RouteMultiradialUpTo/repClass_congr (PROVED)")
  , ("arbitrary log-link iterates do not affect the comparison (deep Ob9)", "B", "named deep statement; NOT formalized (class-level/one-sided laws only)")
  , ("downstream Cor 3.12 consumer context", "interface", "statement corpus 10324-10353; Step (xi) 10750-10987; conclusion 10897") ]

/-- The H7/Ob9 row record has six rows. -/
theorem hullOb9Rows_length : hullOb9Rows.length = 6 := rfl

#check HullOb9Inputs
#check hull_ob9_interface
#check hull_ob9_repClass_congr
#check hullOb9Rows_length

end LeanFormal.IUT.XiFPaper.Hull08Ob9LogLinkActual
end