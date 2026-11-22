import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2715B1LiteralProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe ua uv upi umon ui uR

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The label-distinct prime-strip family obtained from the actual Hodge-theater
family: the capsule label `(j,i)` selects the theater at index `(j,i)`, not a
constant theater.  This uses only actual `OriginalInput.theaterAt` data. -/
noncomputable def distinctPrimeStripOf : PrimeStripOf l V where
  theater := fun j i => I.theaterAt (j.val : Int) (i.val : Int)

@[simp] theorem distinctPrimeStripOf_theater (j : Fin (capsuleLevels l))
    (i : Capsule j.val) :
    (distinctPrimeStripOf I).theater j i =
      I.theaterAt (j.val : Int) (i.val : Int) := rfl

theorem distinctPrimeStripOf_label_injective
    (j : Fin (capsuleLevels l)) :
    Function.Injective
      (fun i : Capsule j.val =>
        (distinctPrimeStripOf I).theater j i) := by
  intro i i' h
  have h' := (I.theaterAt_eq_iff).mp h
  exact Fin.ext (by exact_mod_cast h'.2)

/-- The corresponding actual procession with arithmetic level `n`. -/
noncomputable def distinctProcession (n : Int) : Procession l V where
  toPrimeStripOf := distinctPrimeStripOf I
  n := n

/-- The minimal actual capsule contract: label-distinct procession from the
actual Hodge theaters, plus the canonical one-point log-shell model.  The
log-shell side is actual but not yet the paper-faithful completion log-shell;
`DPrimeStrip`/`FPrimeStrip` do not contain additive local modules, so a faithful
`LogShellFamily` cannot be derived from them alone. -/
noncomputable def distinctCapsuleContract (R : Type uR) [CommSemiring R] :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, uR, 0, 0, uR} R l V I where
  procession := distinctProcession I 0
  VQ := PUnit
  place := fun _ => PUnit
  fintypePlace := fun _ => inferInstance
  logShell := fun j => unitLogShellFamily R j.val
  polyIso := fun j => PolyIsoAction.refl (unitLogShellFamily R j.val)

theorem distinctCapsuleContract_nonempty (R : Type uR) [CommSemiring R] :
    Nonempty
      (SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, uR, 0, 0, uR}
        R l V I) :=
  ⟨distinctCapsuleContract I R⟩

#check distinctPrimeStripOf
#check distinctPrimeStripOf_label_injective
#check distinctProcession
#check distinctCapsuleContract
#check distinctCapsuleContract_nonempty
#print axioms distinctPrimeStripOf_label_injective
#print axioms distinctCapsuleContract_nonempty

end LeanFormal.IUT.XiFPaper.S2715B1LiteralProcessionActual
end
