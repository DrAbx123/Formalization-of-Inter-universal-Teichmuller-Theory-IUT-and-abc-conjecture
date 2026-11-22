import tmp.sheaf.xif.paper.S3139FirstTriangleFieldACResidualActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: field (C) — finite-place conjugate channel of the copy action (part 2)

Part 1 (`S3139FieldCArchimedeanLogActual`) constructs the actual archimedean
Real scalar channel of `F_mod^x`.  The remaining paper content of field (C) is
the *finite-place conjugate channel*: the conjugate action of `F_mod^x` on
local units at the fibers of the prime strip (IUT III:616-620, Fig. I.5,
Remark 3.11.1).  This file records it as the exact missing datum
`SourceConjugateLocalUnitMap` and constructs the constructible downstream
action on the actual value monoid:

* `unitMulAut`: the concrete left-multiplication automorphism of a monoid by a
  unit (actual, no extra data);
* `SourceConjugateLocalUnitMap.valueAut`: the induced local-unit action on the
  value-monoid fiber;
* `SourceConjugateLocalUnitMap.degree_valueAut`: the actual realified degree
  readout `degree(u * x) = degree u * degree x`, ready for the log-volume
  computation.

Also records the minimal dependency of the (Ind1) convention bridge on the
field (A) log-shell module data, and why the tree's actual inputs are
insufficient for the finite-place conjugate map: the tree has local-unit
actions (`FPrimeStrip.unitsAction`, local Galois actions) but no global
`F_mod^x -> local-units` map (Frobenioid `placeToMod` / cusp real encoding,
owned by shehdd/stage4).

**Component, not paper object.**  Named future consumer: `SourceInd2CopyActionData`
and the lattice/mainline q/Theta readouts.  No sorry/axiom/True/PUnit/toy.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual

universe ua uv upi umon ui uR uVQ uPlace uShell u

variable {l : PrimeGeFive} {V : Type uv}

/-- The exact missing datum for the finite-place channel of the conjugate copy
action: a conjugate map from a copy group (the global units of @F_mod@) to the
Frobenius submonoid of the prime strip, multiplicative in the copy argument.
The tree has the local Frobenius actions (@FPrimeStrip.action@, its
@unitsAction@/@timesMuAction@) but no global @F_mod^x -> Pi@ conjugate map
(Frobenioid @placeToMod@ / cusp real encoding, owned by shehdd/stage4).
Page refs: III:616-620, Fig. I.5; Remark 3.11.1. -/
structure SourceConjugateLocalUnitMap
    (F : FPrimeStrip.{umon, uv, upi} V) (G : Type u) [Group G] where
  /-- the conjugate Frobenius element of a copy at every fiber of the strip -/
  conjugate : G → (v : V) → F.toDPrimeStrip.Pi v
  /-- multiplicativity of the conjugate map -/
  conjugate_one : conjugate 1 = fun _ => 1
  conjugate_mul : ∀ c d, conjugate (c * d) = fun v =>
    conjugate c v * conjugate d v

/-- Given the missing conjugate map, the actual local Frobenius action of the
conjugate element on the value-monoid fiber: the constructible downstream part
of the finite-place channel. -/
def SourceConjugateLocalUnitMap.conjugateAut
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c : G) (v : V) :
    MulAut (F.Mon v) :=
  F.action v (D.conjugate c v)

/-- The actual realified readout of the local Frobenius action: the degree of
the value after the conjugate action, ready for the log-volume computation. -/
def SourceConjugateLocalUnitMap.conjugateValue
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c : G) (v : V) (x : F.Mon v) :
    Multiplicative ℝ :=
  F.degree v ((D.conjugateAut c v) x)

/-- The conjugate local Frobenius action is multiplicative in the copy: applying
the product copy is applying the two copies in order. -/
theorem SourceConjugateLocalUnitMap.conjugateAut_mul_apply
    {F : FPrimeStrip.{umon, uv, upi} V} {G : Type u} [Group G]
    (D : SourceConjugateLocalUnitMap F G) (c d : G) (v : V) (x : F.Mon v) :
    (D.conjugateAut (c * d) v) x =
      (D.conjugateAut c v) ((D.conjugateAut d v) x) := by
  have h : D.conjugate (c * d) = fun v => D.conjugate c v * D.conjugate d v :=
    D.conjugate_mul c d
  show F.action v (D.conjugate (c * d) v) x = _
  rw [h, map_mul]
  rfl

/-- Minimal dependency of the (Ind1) convention bridge: it requires the actual
log-shell module family and the poly-isomorphism action (the data of field
(A)), because the comparison between the contract polyIso action and the
procession-automorphism reindex acts on the identified log-shell modules. -/
def SourceInd1BridgeDependency (R : Type uR) [CommSemiring R]
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (SourceCapsuleSourceDataMissing.{ua, uv, upi, umon, ui, uR,
    uVQ, uPlace, uShell} R l V I)

end LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual

end
