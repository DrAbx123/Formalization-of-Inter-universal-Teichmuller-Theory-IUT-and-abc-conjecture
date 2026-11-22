import tmp.sheaf.xif.paper.S3139FieldCConjugateActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: C2 reduction — the finite-place conjugate channel reduces to the local element map

The C2 residual is the finite-place conjugate channel: a map from the global
units of `F_mod` to local units at the fibers of the prime strip (IUT III:616-620,
Fig. I.5, Remark 3.11.1).  This file reduces it to the exact missing datum and
constructs the realified scalar channel that the copy action actually needs:

* `SourceFmodLocalElementMap`: the exact missing datum — a multiplicative map
  from `(F_mod)^x` to the local value-monoid units `(F.Mon v)^x` at every fiber;
* `SourceFmodLocalElementMap.localDegree`: its actual realified degree, i.e. the
  multiplicative character of `(F_mod)^x` into `Multiplicative R` at each fiber;
* `localDegree_additive` / `localDegree_unit`: the realified additive scalar
  channel `R` and the induced `R^x`-valued character (the only data the
  realified copy action consumes).

The tree provides the *local* actions (`FPrimeStrip.action`, local Frobenius
groups, `FPrimeStrip.degree`) but no global-to-local element map: that is the
missing placeToMod/cusp alignment owned together with shehdd/stage4.

**Component, not paper object.**  Named consumer: the finite-place copy action
(`SourceInd2CopyActionData`) and the archimedean Real character.  No
sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The exact missing datum of C2: a multiplicative map from the global units of
the actual `F_mod` to the local value-monoid units at every fiber of the prime
strip (the conjugate local-unit map; placeToMod/cusp alignment, III:616-620). -/
structure SourceFmodLocalElementMap
    (F : FPrimeStrip.{umon, uv, upi} V)
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{ui} l) where
  /-- the local unit of the conjugate copy at every fiber -/
  conjugate : (A.Fmod)ˣ → (v : V) → (F.Mon v)ˣ
  conjugate_one : conjugate 1 = fun _ => 1
  conjugate_mul : ∀ c d : (A.Fmod)ˣ, conjugate (c * d) = fun v =>
    conjugate c v * conjugate d v

namespace SourceFmodLocalElementMap

variable {F : FPrimeStrip.{umon, uv, upi} V}
variable {A : LeanFormal.IUT.InitialThetaArithmeticData.{ui} l}

/-- The actual realified degree of the conjugate local unit: the multiplicative
character of `(F_mod)^x` into `Multiplicative R` at each fiber. -/
def localDegree (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (c : (A.Fmod)ˣ) (v : V) : Multiplicative ℝ :=
  F.degree v (D.conjugate c v : F.Mon v)

/-- The realified degree is multiplicative in the global unit (the character
law of the conjugate channel). -/
theorem localDegree_mul (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (c d : (A.Fmod)ˣ) (v : V) :
    D.localDegree (c * d) v = D.localDegree c v * D.localDegree d v := by
  have h : (D.conjugate (c * d) v : F.Mon v) =
      (D.conjugate c v : F.Mon v) * (D.conjugate d v : F.Mon v) := by
    rw [D.conjugate_mul]
    rfl
  show F.degree v (D.conjugate (c * d) v : F.Mon v) = _
  rw [h, map_mul]
  rfl

/-- The realified degree of the unit copy is one. -/
theorem localDegree_one (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (v : V) : D.localDegree 1 v = 1 := by
  have h : (D.conjugate 1 v : F.Mon v) = 1 := by
    rw [D.conjugate_one]
    rfl
  show F.degree v (D.conjugate 1 v : F.Mon v) = 1
  rw [h, map_one]

/-- The realified additive scalar channel at one fiber. -/
def localDegreeAdd (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (c : (A.Fmod)ˣ) (v : V) : ℝ :=
  Multiplicative.toAdd (D.localDegree c v)

/-- The additive scalar channel is additive in the global unit. -/
theorem localDegreeAdd_mul (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (c d : (A.Fmod)ˣ) (v : V) :
    D.localDegreeAdd (c * d) v = D.localDegreeAdd c v + D.localDegreeAdd d v := by
  show Multiplicative.toAdd (D.localDegree (c * d) v) = _
  rw [D.localDegree_mul]
  rfl

/-- The induced `R^x`-valued scalar character at one fiber: exponentiate the
additive realified degree (a positive Real unit). -/
def localScalarUnit (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (c : (A.Fmod)ˣ) (v : V) : ℝˣ :=
  Units.mk0 (Real.exp (D.localDegreeAdd c v)) (ne_of_gt (Real.exp_pos _))

/-- The induced Real unit of the product copy is the product of the units. -/
theorem localScalarUnit_mul (D : SourceFmodLocalElementMap (l := l) (V := V) F A)
    (c d : (A.Fmod)ˣ) (v : V) :
    D.localScalarUnit (c * d) v = D.localScalarUnit c v * D.localScalarUnit d v := by
  apply Units.ext
  show Real.exp (D.localDegreeAdd (c * d) v) =
    Real.exp (D.localDegreeAdd c v) * Real.exp (D.localDegreeAdd d v)
  rw [D.localDegreeAdd_mul, Real.exp_add]

end SourceFmodLocalElementMap

end LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual

end
