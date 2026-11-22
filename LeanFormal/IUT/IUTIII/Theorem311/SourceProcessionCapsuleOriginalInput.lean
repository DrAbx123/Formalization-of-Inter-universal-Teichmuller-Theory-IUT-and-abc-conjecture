import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilySourceReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Processions from the original source family

The source input contains an actual Hodge-theater family indexed, up to
equivalence, by `Int x Int`, together with a chosen theater and its prime
strip at every pair `(n,m)`.  This file uses the theaters themselves, rather
than repeating one theater constantly over all capsule labels.

There is no map in `OriginalInput` from a capsule label to a pair `(n,m)` of
the source family.  Such a map is therefore recorded explicitly as a
`CapsuleTheaterAssignment`; the nontriviality statements take its
nonconstancy as a theorem premise.  The canonical assignment supplied below
is an explicit data-layer choice, not the paper's construction of the
procession assignment.

What comes from `OriginalInput`: every theater, every prime strip, the
arithmetic alignment, and the distinctness of the family.  What remains
additional named data: the capsule-to-source index assignment, the valuation
set, the place types, the log-shell modules, and the poly-isomorphism action.

This file does not assert a Gaussian object, does not close N4 or N5, and
does not state a final log-volume inequality.
-/

namespace LeanFormal.IUT
namespace Theorem311Source
namespace SourceProcessionCapsule

noncomputable section

universe ua uv upi umon ui uR uVQ uPlace uShell

/-! ## 1. Capsule labels selected in the original family -/

/-- The source family has at least the two capsule levels `0` and `1`. -/
theorem one_lt_capsuleLevels (l : PrimeGeFive) : 1 < capsuleLevels l := by
  have hfour : 4 <= l.value + 1 := by
    have hfive := l.ge_five
    omega
  have htwo : 2 <= (l.value + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  unfold capsuleLevels lPlus
  omega

/-- An explicit selection of a source theater for every capsule label.

    `OriginalInput` does not provide this selection.  It is the minimal extra
    data needed to turn the actual `Int x Int` theater family into a
    capsule-indexed family. -/
structure CapsuleTheaterAssignment
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  index : (j : Fin (capsuleLevels l)) -> Capsule j.val ->
    SourceTheorem311Index

namespace CapsuleTheaterAssignment

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The selected source theater is not constant on one capsule. -/
def Nonconstant (A : CapsuleTheaterAssignment l V I) : Prop :=
  exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
    A.index j i ≠ A.index j i'

/-- The actual source theater selected at a capsule label. -/
def toTheater (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    HodgeTheater.{ua, uv, upi, umon} l V :=
  I.theaterAt (A.index j i).1 (A.index j i).2

/-- The capsule-indexed family of actual source theaters. -/
def toPrimeStripOf (A : CapsuleTheaterAssignment l V I) :
    PrimeStripOf.{ua, uv, upi, umon} l V where
  theater := fun j i => A.toTheater j i

/-- The resulting procession, retaining the arithmetic-holomorphic index. -/
def toProcession (A : CapsuleTheaterAssignment l V I) (n : Int) :
    Procession.{uv, umon, upi, ua} l V where
  toPrimeStripOf := A.toPrimeStripOf
  n := n

@[simp] theorem toTheater_apply (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    A.toTheater j i =
      I.theaterAt (A.index j i).1 (A.index j i).2 := rfl

@[simp] theorem toPrimeStripOf_theater (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    A.toPrimeStripOf.theater j i =
      I.theaterAt (A.index j i).1 (A.index j i).2 := rfl

@[simp] theorem toPrimeStripOf_primeStrip
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    A.toPrimeStripOf.primeStrip j i =
      I.primeStripAt (A.index j i).1 (A.index j i).2 := rfl

@[simp] theorem toProcession_toPrimeStripOf
    (A : CapsuleTheaterAssignment l V I) (n : Int) :
    (A.toProcession n).toPrimeStripOf = A.toPrimeStripOf := rfl

@[simp] theorem toProcession_n
    (A : CapsuleTheaterAssignment l V I) (n : Int) :
    (A.toProcession n).n = n := rfl

/-- Distinct selected source indices give distinct actual theaters. -/
theorem theaterAt_ne_of_index_ne
    {p q : SourceTheorem311Index} (h : p ≠ q) :
    I.theaterAt p.1 p.2 ≠ I.theaterAt q.1 q.2 := by
  intro hEq
  apply h
  exact Prod.ext_iff.mpr (I.theaterAt_eq_iff.mp hEq)

/-- Under arithmetic alignment, distinct source indices also give distinct
    actual prime strips. -/
theorem primeStripAt_ne_of_index_ne
    {p q : SourceTheorem311Index} (h : p ≠ q) :
    I.primeStripAt p.1 p.2 ≠ I.primeStripAt q.1 q.2 := by
  have hidx : OriginalInput.indexOf I p.1 p.2 ≠
      OriginalInput.indexOf I q.1 q.2 := by
    intro hEq
    exact h (OriginalInput.indexOf_injective I hEq)
  have hstrip := primeStrip_ne_of_index_ne_of_arithmetic_eq
    I.family (fun i => I.arithmetic_alignment i) hidx
  simpa [OriginalInput.primeStripAt, OriginalInput.theaterAt] using hstrip

/-- Nonconstancy of the selection produces nonconstant actual theaters. -/
theorem exists_theater_ne (A : CapsuleTheaterAssignment l V I)
    (hA : A.Nonconstant) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      A.toPrimeStripOf.theater j i ≠ A.toPrimeStripOf.theater j i' := by
  obtain ⟨j, i, i', hne⟩ := hA
  exact ⟨j, i, i', theaterAt_ne_of_index_ne hne⟩

/-- Nonconstancy of the selection produces nonconstant actual prime strips. -/
theorem exists_primeStrip_ne (A : CapsuleTheaterAssignment l V I)
    (hA : A.Nonconstant) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      A.toPrimeStripOf.primeStrip j i ≠
        A.toPrimeStripOf.primeStrip j i' := by
  obtain ⟨j, i, i', hne⟩ := hA
  exact ⟨j, i, i', primeStripAt_ne_of_index_ne hne⟩

end CapsuleTheaterAssignment

/-! ## 2. A concrete nonconstant selection -/

/-- The chosen data-layer dictionary `(j,i) |-> (i,n)` into the source
    `Int x Int` index.  This is a witness, not a paper-derived dictionary. -/
def canonicalCapsuleTheaterAssignment
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    CapsuleTheaterAssignment l V I where
  index := fun _ i => (Int.ofNat i.val, n)

namespace canonicalCapsuleTheaterAssignment

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem nonconstant (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Int) :
    (canonicalCapsuleTheaterAssignment I n).Nonconstant := by
  refine ⟨⟨1, one_lt_capsuleLevels l⟩,
    ⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ?_⟩
  intro h
  have hfst : (0 : Int) = 1 := congrArg Prod.fst h
  norm_num at hfst

theorem theater_nontrivial
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      (canonicalCapsuleTheaterAssignment I n).toPrimeStripOf.theater j i ≠
        (canonicalCapsuleTheaterAssignment I n).toPrimeStripOf.theater j i' :=
  (canonicalCapsuleTheaterAssignment I n).exists_theater_ne
    (nonconstant I n)

theorem primeStrip_nontrivial
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      (canonicalCapsuleTheaterAssignment I n).toPrimeStripOf.primeStrip j i ≠
        (canonicalCapsuleTheaterAssignment I n).toPrimeStripOf.primeStrip j i' :=
  (canonicalCapsuleTheaterAssignment I n).exists_primeStrip_ne
    (nonconstant I n)

end canonicalCapsuleTheaterAssignment

/-! ## 3. Filling the contract from the source family -/

/-- The additional choices which the current `OriginalInput` does not supply:
    the capsule-to-source index assignment, the valuation/place basis, the
    log-shell modules, and the poly-isomorphism actions. -/
structure OriginalInputCapsuleData
    (R : Type uR) [CommSemiring R]
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  assignment : CapsuleTheaterAssignment l V I
  n : Int
  VQ : Type uVQ
  place : VQ -> Type uPlace
  fintypePlace : forall vQ, Fintype (place vQ)
  logShell : (j : Fin (capsuleLevels l)) ->
    LogShellFamily.{uR, uVQ, uPlace, uShell} R place j.val
  polyIso : (j : Fin (capsuleLevels l)) ->
    PolyIsoAction.{uR, uVQ, uPlace, uShell} (logShell j)

namespace SourceProcessionCapsuleContract

/-- The data-layer contract whose procession is built from the actual source
    theaters selected by `D.assignment`. -/
def ofOriginalInput
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : OriginalInputCapsuleData.{ua, uv, upi, umon, ui,
      uR, uVQ, uPlace, uShell} R l V I) :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui,
      uR, uVQ, uPlace, uShell} R l V I where
  procession := D.assignment.toProcession D.n
  VQ := D.VQ
  place := D.place
  fintypePlace := D.fintypePlace
  logShell := D.logShell
  polyIso := D.polyIso

@[simp] theorem ofOriginalInput_procession
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : OriginalInputCapsuleData.{ua, uv, upi, umon, ui,
      uR, uVQ, uPlace, uShell} R l V I) :
    (ofOriginalInput R I D).procession = D.assignment.toProcession D.n := rfl

end SourceProcessionCapsuleContract

/-- The one-point log-shell completion of an explicitly selected source
    assignment.  The theater and prime-strip part is still the actual
    `OriginalInput` family; only the log-shell part is the one-point model. -/
def unitOriginalInputCapsuleData
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    OriginalInputCapsuleData.{ua, uv, upi, umon, ui, uR, 0, 0, uR}
      R l V I where
  assignment := canonicalCapsuleTheaterAssignment I n
  n := n
  VQ := PUnit
  place := fun _ => PUnit
  fintypePlace := fun _ => inferInstance
  logShell := fun j => unitLogShellFamily R j.val
  polyIso := fun j => PolyIsoAction.refl (unitLogShellFamily R j.val)

theorem originalInputContract_nonempty
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Nonempty (SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui,
      uR, 0, 0, uR} R l V I) :=
  ⟨SourceProcessionCapsuleContract.ofOriginalInput R I
    (unitOriginalInputCapsuleData R I 0)⟩

/-- The contract witness has a genuinely nonconstant theater family. -/
theorem originalInputContract_theater_nontrivial
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((SourceProcessionCapsuleContract.ofOriginalInput R I
          (unitOriginalInputCapsuleData R I 0)).procession).toPrimeStripOf.theater
          j i ≠
        ((SourceProcessionCapsuleContract.ofOriginalInput R I
          (unitOriginalInputCapsuleData R I 0)).procession).toPrimeStripOf.theater
          j i' := by
  simpa [SourceProcessionCapsuleContract.ofOriginalInput,
    unitOriginalInputCapsuleData] using
    canonicalCapsuleTheaterAssignment.theater_nontrivial I 0

/-- The contract witness has genuinely nonconstant prime strips. -/
theorem originalInputContract_primeStrip_nontrivial
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((SourceProcessionCapsuleContract.ofOriginalInput R I
          (unitOriginalInputCapsuleData R I 0)).procession).toPrimeStripOf.primeStrip
          j i ≠
        ((SourceProcessionCapsuleContract.ofOriginalInput R I
          (unitOriginalInputCapsuleData R I 0)).procession).toPrimeStripOf.primeStrip
          j i' := by
  simpa [SourceProcessionCapsuleContract.ofOriginalInput,
    unitOriginalInputCapsuleData] using
    canonicalCapsuleTheaterAssignment.primeStrip_nontrivial I 0

end

end SourceProcessionCapsule
end Theorem311Source
end LeanFormal.IUT
