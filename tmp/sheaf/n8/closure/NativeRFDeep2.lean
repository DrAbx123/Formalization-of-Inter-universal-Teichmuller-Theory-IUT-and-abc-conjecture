import tmp.sheaf.n8.closure.NativeBindingRFActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

/-!
# Native RF deep attempt 2: nontrivial posRealAction and exact obstruction

This is a write-only attempt to go beyond the constant q = 1 case of
NativeRFProof.  It reuses the exact source-field packages of
NativeBindingRFActual.

The obstruction found is:

* every SourceImageRealization at the native selected bad place produces a
  value point x = posRealAction (ofAdd (log q)) with
  logDegreeAt x = log q;
* consequently, if the native degree map at that place is identically zero,
  then any such realization forces q = 1;
* hence there is no nontrivial realization on a zero-degree fiber.  The exact
  missing primitive is a positive-real action whose q-value has nonzero
  degree; no production object supplies it.

No arbitrary function, no V = Unit surrogate, and no fake axiom is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeRFDeep2

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeBindingRFActual
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable (I : OriginalInput l (NativePlaces X.S))

/-- Reused actual selected native place. -/
abbrev nativeSelectedPlace : NativePlaces X.S :=
  NativeBindingRFActual.nativeSelectedPlace X

/-! ## 1. Exact image-field reduction -/

/-- A realization gives the exact two fields. -/
def imageFieldsOfRealization
    (R : I.SourceImageRealization (nativeSelectedPlace X)) :
    NativeImageRealizationSourceFields X I where
  posRealAction := R.posRealAction
  degree_of_q := R.degree_of_q

/-- The exact two fields give a realization. -/
def realizationOfImageFields
    (R : NativeImageRealizationSourceFields X I) :
    I.SourceImageRealization (nativeSelectedPlace X) :=
  NativeBindingRFActual.nativeImageRealizationOfFields X I R

theorem imageFields_nonempty_iff :
    Nonempty (NativeImageRealizationSourceFields X I) ↔
      Nonempty (I.SourceImageRealization (nativeSelectedPlace X)) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨realizationOfImageFields (X := X) I R⟩
  · rintro ⟨R⟩
    exact ⟨imageFieldsOfRealization (X := X) I R⟩

/-! ## 2. The q = 1 actual construction (constant action) -/

def trivialPositiveRealAction (v : NativePlaces X.S) :
    Multiplicative Real →* I.ValueMonoidAt 0 0 v :=
  1

theorem logDegreeAt_trivialPositiveRealAction
    (v : NativePlaces X.S) (x : Multiplicative Real) :
    I.logDegreeAt 0 0 v (trivialPositiveRealAction (X := X) I v x) = 0 := by
  change I.logDegreeAt 0 0 v (1 : I.ValueMonoidAt 0 0 v) = 0
  exact I.logDegreeAt_one 0 0 v

/-- Genuine native-place construction when q = 1. -/
def realizationOfQOne
    (hq : (I.theaterAt 0 0).thetaPacket.q = 1) :
    I.SourceImageRealization (nativeSelectedPlace X) where
  posRealAction := trivialPositiveRealAction (X := X) I (nativeSelectedPlace X)
  degree_of_q := by
    simp [trivialPositiveRealAction, hq, I.logDegreeAt_one]

theorem nonempty_realization_of_q_one
    (hq : (I.theaterAt 0 0).thetaPacket.q = 1) :
    Nonempty (I.SourceImageRealization (nativeSelectedPlace X)) :=
  ⟨realizationOfQOne (X := X) I hq⟩

/-! ## 3. The exact degree point forced by any realization -/

def degreePointOfRealization
    (R : I.SourceImageRealization (nativeSelectedPlace X)) :
    I.ValueMonoidAt 0 0 (nativeSelectedPlace X) :=
  R.posRealAction (Multiplicative.ofAdd
    (Real.log ((I.theaterAt 0 0).thetaPacket.q)))

theorem degreePointOfRealization_degree
    (R : I.SourceImageRealization (nativeSelectedPlace X)) :
    I.logDegreeAt 0 0 (nativeSelectedPlace X)
        (degreePointOfRealization (X := X) I R) =
      Real.log ((I.theaterAt 0 0).thetaPacket.q) :=
  R.degree_of_q

/-- Any realization forces the q-degree point to have degree log q. -/
theorem exists_degreePoint_eq_log
    (R : I.SourceImageRealization (nativeSelectedPlace X)) :
    ∃ x : I.ValueMonoidAt 0 0 (nativeSelectedPlace X),
      I.logDegreeAt 0 0 (nativeSelectedPlace X) x =
        Real.log ((I.theaterAt 0 0).thetaPacket.q) :=
  ⟨degreePointOfRealization (X := X) I R,
    degreePointOfRealization_degree (X := X) I R⟩

/-! ## 4. Exact obstruction for zero native degree -/

/-- If the native degree map at the selected bad place is identically zero,
then any SourceImageRealization forces q = 1. -/
theorem q_eq_one_of_logDegree_zero
    (hdeg : ∀ x : I.ValueMonoidAt 0 0 (nativeSelectedPlace X),
      I.logDegreeAt 0 0 (nativeSelectedPlace X) x = 0)
    (R : I.SourceImageRealization (nativeSelectedPlace X)) :
    (I.theaterAt 0 0).thetaPacket.q = 1 := by
  have hlog : Real.log ((I.theaterAt 0 0).thetaPacket.q) = 0 := by
    rw [← R.degree_of_q]
    exact hdeg _
  have hqpos : 0 < (I.theaterAt 0 0).thetaPacket.q :=
    (I.theaterAt 0 0).thetaPacket.q_pos
  rcases (Real.log_eq_zero.mp hlog) with hzero | hone | hneg
  · linarith
  · exact hone
  · linarith

/-- On a native fiber whose degree is identically zero on the value monoid, a
nontrivial q cannot carry a SourceImageRealization. -/
theorem no_realization_of_q_ne_one_and_logDegree_zero
    (hdeg : ∀ x : I.ValueMonoidAt 0 0 (nativeSelectedPlace X),
      I.logDegreeAt 0 0 (nativeSelectedPlace X) x = 0)
    (hq : (I.theaterAt 0 0).thetaPacket.q ≠ 1) :
    ¬ Nonempty (I.SourceImageRealization (nativeSelectedPlace X)) := by
  rintro ⟨R⟩
  exact hq (q_eq_one_of_logDegree_zero (X := X) I hdeg R)

/-! ## 5. Exact missing primitive -/

/-- A nontrivial primitive: a positive-real action whose q-value has nonzero
degree.  The degree equation is the exact equation required by
SourceImageRealization; the q ≠ 1 field records that this is not the constant
case. -/
structure NativeNontrivialPosRealActionPrimitive where
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 (nativeSelectedPlace X)
  degree_of_q : I.logDegreeAt 0 0 (nativeSelectedPlace X)
      (posRealAction (Multiplicative.ofAdd
        (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
    Real.log ((I.theaterAt 0 0).thetaPacket.q)
  q_ne_one : (I.theaterAt 0 0).thetaPacket.q ≠ 1

/-- The primitive gives the exact SourceImageRealization at the native
selected place. -/
def realizationOfNontrivialPrimitive
    (P : NativeNontrivialPosRealActionPrimitive (X := X) I) :
    I.SourceImageRealization (nativeSelectedPlace X) where
  posRealAction := P.posRealAction
  degree_of_q := P.degree_of_q

/-- If the primitive exists, the q-degree point has nonzero degree. -/
theorem nontrivialPrimitive_degreePoint_ne_zero
    (P : NativeNontrivialPosRealActionPrimitive (X := X) I) :
    I.logDegreeAt 0 0 (nativeSelectedPlace X)
        (P.posRealAction (Multiplicative.ofAdd
          (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) ≠ 0 := by
  rw [P.degree_of_q]
  exact Real.log_ne_zero_of_pos_of_ne_one
    (I.theaterAt 0 0).thetaPacket.q_pos P.q_ne_one

/-- Exactly: the nontrivial primitive exists iff there is a realization with
q != 1. -/
def nontrivialPrimitiveOfRealization
    (R : I.SourceImageRealization (nativeSelectedPlace X))
    (hq : (I.theaterAt 0 0).thetaPacket.q ≠ 1) :
    NativeNontrivialPosRealActionPrimitive (X := X) I where
  posRealAction := R.posRealAction
  degree_of_q := R.degree_of_q
  q_ne_one := hq

end LeanFormal.IUT.N8Closure.NativeRFDeep2

end