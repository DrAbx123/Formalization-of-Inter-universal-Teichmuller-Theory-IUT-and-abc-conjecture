import tmp.sheaf.xif.paper.S2715B1LiteralProcessionActual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import tmp.sheaf.n8.closure.SourcePilotRegion

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2718LiteralDDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S2715B1LiteralProcessionActual

universe ua uv upi umon ui uR uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The single global valuation used by the literal construction. -/
abbrev LiteralVQ : Type := PUnit

/-- The actual finite places over the single valuation: the dependent sum of
the actual C3 tensor places.  This is a non-trivial place set whenever
`C3.tensorIndex` is non-empty. -/
abbrev LiteralPlace : LiteralVQ -> Type :=
  fun _ => Sigma (fun i : C3.tensorIndex => C3.tensorPlaceIndex i)

/-- The actual local log-shell datum at a literal place: the genuine
common-prime completion of the actual C3 tensor place. -/
noncomputable def literalDatum (v : LiteralPlace (I := I) C3 PUnit.unit) :
    SourceLogShellDatum :=
  sourceLocalLogShellDatum
    (K := I.initial.arithmetic.Fmod) (p := C3.p)
    (C3.tensorPlaces v.1 v.2)

/-- The non-trivial literal log-shell family: each shell is the actual
`IQSpan` of the local log-shell datum at the corresponding completion,
not the one-point `unitLogShellFamily` model. -/
noncomputable def literalLogShellFamily (j : Nat) :
    LogShellFamily (R := Rat) (Place := LiteralPlace (I := I) C3) j where
  Shell := fun _ _ v => (literalDatum I C3 v).IQSpan
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

theorem literalLogShellFamily_shell (j : Nat) (i : Capsule j)
    (vQ : LiteralVQ) (v : LiteralPlace (I := I) C3 vQ) :
    (literalLogShellFamily I C3 j).Shell i vQ v =
      (literalDatum I C3 v).IQSpan := rfl

/-- Every element of the actual `logShell` at a literal place lies in the
literal shell module. -/
theorem actual_logShell_mem_literalLogShellFamily (j : Nat) (i : Capsule j)
    (vQ : LiteralVQ) (v : LiteralPlace (I := I) C3 vQ)
    {x : (literalDatum I C3 v).K}
    (hx : (literalDatum I C3 v).logShell x) :
    ((literalDatum I C3 v).IQSpan : Set (literalDatum I C3 v).K) x :=
  SourceLogShellDatum.logShell_subset_IQSpan (literalDatum I C3 v) hx

/-- The actual non-trivial `LiteralDData`: distinct procession from the actual
Hodge-theater family, actual completion log-shell family, and the identity
poly-isomorphism action. -/
noncomputable def literalDData :
    SourceProcessionCapsuleContract (R := Rat) l V I where
  procession := distinctProcession I 0
  VQ := LiteralVQ
  place := LiteralPlace (I := I) C3
  fintypePlace := fun _ => inferInstance
  logShell := fun j => literalLogShellFamily I C3 j.val
  polyIso := fun j => PolyIsoAction.refl (literalLogShellFamily I C3 j.val)

theorem literalDData_logShell (j : Fin (capsuleLevels l)) :
    (literalDData I C3).logShell j = literalLogShellFamily I C3 j.val := rfl

#check LiteralVQ
#check LiteralPlace
#check literalDatum
#check literalLogShellFamily
#check actual_logShell_mem_literalLogShellFamily
#check literalDData
#check literalDData_logShell
#print axioms literalLogShellFamily_shell
#print axioms literalDData_logShell

end LeanFormal.IUT.XiFPaper.S2718LiteralDDataActual
end
