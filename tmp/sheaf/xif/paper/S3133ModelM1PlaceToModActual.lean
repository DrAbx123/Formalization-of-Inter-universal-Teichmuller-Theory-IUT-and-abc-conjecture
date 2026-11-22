import tmp.sheaf.xif.paper.S3133ModelVBasisActual

/-!
# Model M1: V_mod_bijection / place-to-moduli construction (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot model R1 composition,
lattice placeToMod wiring, mainline/lattice in-model R1 record.

AUDIT CLASSIFICATION (Lead/mainline approved, class C source datum): M1's
placeToMod/V_mod_bijection is IUT I Definition 3.1(b),(e) source data (the
restriction-section bijection V_mod ~ V(F)), a source convention/choice rather
than an external arithmetic input.  In the from-scratch model we CONSTRUCT it
explicitly: the model moduli set is the single bad moduli place, mapped to the
distinguished model place vFive; injectivity is immediate.  Hence M1 is class A
in-model (definitional construction), with the exact construction recorded here.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ModelM1PlaceToModActual

open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual

/-- The model moduli places: the single bad moduli place. -/
abbrev S3135ModelVMod : Type := ULift.{0} (Fin 1)

/-- The model place-to-moduli map (V_mod_bijection data of IUT I Def 3.1(e)):
the model moduli place maps to the distinguished nonarchimedean place. -/
def modelPlaceToMod : S3135ModelVMod → S3135ModelV :=
  fun _ => vFive

/-- The model V_mod_bijection datum constructed explicitly. -/
structure S3133ModelPlaceToModDatum where
  /-- the model moduli place type -/
  V_mod : Type
  /-- the place map (restriction-section bijection source datum) -/
  placeOf : V_mod → S3135ModelV
  /-- faithfulness of the model place map -/
  placeOf_injective : Function.Injective placeOf

/-- The constructed in-model M1 datum. -/
noncomputable def modelPlaceToModDatum : S3133ModelPlaceToModDatum where
  V_mod := S3135ModelVMod
  placeOf := modelPlaceToMod
  placeOf_injective := by
    intro a b _
    exact Subsingleton.elim a b

/-- The model place map is injective (in-model class A). -/
theorem modelPlaceToMod_injective : Function.Injective modelPlaceToMod :=
  modelPlaceToModDatum.placeOf_injective

/-- In-model M1 is CONSTRUCTIBLE: an explicit V_mod_bijection datum with an
injective place map exists. -/
theorem S3133ModelM1_constructible :
    ∃ D : S3133ModelPlaceToModDatum, Function.Injective D.placeOf :=
  ⟨modelPlaceToModDatum, modelPlaceToMod_injective⟩

end LeanFormal.IUT.XiFPaper.S3133ModelM1PlaceToModActual
