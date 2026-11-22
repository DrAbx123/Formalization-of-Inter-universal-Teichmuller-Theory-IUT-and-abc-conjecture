import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem
import tmp.sheaf.xif.paper.Mzk1HodgeToTakkunFieldsActual

/-! Mainline (A511-2): label-management object reuse.  We build the Takkun
`LabeledPrimeStripSystem` (the symmetrization-isomorphism prime-strip system used by the
Hodge theater) from our `DPrimeStrip` by reusing the existing real Takkun definition
`constantLabeledSystem`; no new data, no shell. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripLabeledActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT

/-- The labeled prime-strip system of a single strip: all labels carry our translated
  strip and the symmetrizing isomorphisms are its reflexive equivalence. -/
def takkunLabeledSystemOfOur {V L Sym : Type*} [Group Sym] [MulAction Sym L]
    (D : LeanFormal.IUT.DPrimeStrip V) :
    IUT.Frobenioid.LabeledPrimeStripSystem.{0} V L Sym :=
  IUT.Frobenioid.constantLabeledSystem V L Sym (takkunDOfOur D)

@[simp] theorem takkunLabeledSystemOfOur_strip {V L Sym : Type*} [Group Sym]
    [MulAction Sym L] (D : LeanFormal.IUT.DPrimeStrip V) (t : L) :
    (takkunLabeledSystemOfOur D).strip t = takkunDOfOur D := rfl

@[simp] theorem takkunLabeledSystemOfOur_symIso {V L Sym : Type*} [Group Sym]
    [MulAction Sym L] (D : LeanFormal.IUT.DPrimeStrip V) (s : Sym) (t : L) :
    (takkunLabeledSystemOfOur D).symIso s t =
      IUT.Frobenioid.DPrimeStripEquiv.refl (takkunDOfOur D) := rfl

/-- The label-management data attached to our Hodge theater (via its prime strip). -/
def takkunHodgeLabeledSystem {l : PrimeGeFive} {V L Sym : Type} [Group Sym]
    [MulAction Sym L] (h : LeanFormal.IUT.HodgeTheater.{0, 0, 0, 0} l V) :
    IUT.Frobenioid.LabeledPrimeStripSystem.{0} V L Sym :=
  takkunLabeledSystemOfOur h.primeStrip.toDPrimeStrip

end

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripLabeledActual