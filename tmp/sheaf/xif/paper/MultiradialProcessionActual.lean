import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTIII.Theorem311.SourceLGPMonoidLayer

/-!
# Actual source procession and Ind1 tensor action

This file builds the procession data from the actual source link system
`I.linkAt`: members are actual F-prime-strips, transitions are the actual
prime-strip equivalences, and automorphisms are capsule permutations with the
actual strip links.  The actual (Ind1) action on the tensor packet is the
contract's `PolyIsoAction.tensorMap`.

No inequality, equality judgement, arbitrary data, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace MultiradialProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

def PrcMember
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    FPrimeStrip V :=
  (A.toTheater j i).primeStrip

def PrcTransition
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i i' : Capsule j.val) :
    FPrimeStripEquiv (PrcMember A j i) (PrcMember A j i') :=
  (I.linkAt (A.index j i).1 (A.index j i).2
    (A.index j i').1 (A.index j i').2).primeStripEquiv

theorem PrcTransition_refl
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    PrcTransition A j i i = FPrimeStripEquiv.refl (PrcMember A j i) := by
  unfold PrcTransition
  rw [I.linkAt_refl]
  rfl

theorem PrcTransition_trans
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i i' i'' : Capsule j.val) :
    FPrimeStripEquiv.trans (PrcTransition A j i i')
        (PrcTransition A j i' i'') =
      PrcTransition A j i i'' := by
  unfold PrcTransition
  have h := congrArg HodgeTheaterLink.primeStripEquiv
    (I.linkAt_trans (A.index j i).1 (A.index j i).2
      (A.index j i').1 (A.index j i').2
      (A.index j i'').1 (A.index j i'').2)
  simpa [PrcMember, HodgeTheaterLink.trans] using h

structure PrcAutomorphism
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) where
  perm : Capsule j.val ≃ Capsule j.val
  component : forall i : Capsule j.val,
    FPrimeStripEquiv (PrcMember A j i) (PrcMember A j (perm i))

def PrcAutomorphism.ofPerm
    (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (sigma : Capsule j.val ≃ Capsule j.val) :
    PrcAutomorphism A j where
  perm := sigma
  component := fun i => PrcTransition A j i (sigma i)

def PrcAutomorphism.id
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l)) :
    PrcAutomorphism A j :=
  PrcAutomorphism.ofPerm A j (Equiv.refl (Capsule j.val))

def PrcAutomorphism.comp
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (sigma tau : PrcAutomorphism A j) : PrcAutomorphism A j where
  perm := sigma.perm.trans tau.perm
  component := fun i =>
    FPrimeStripEquiv.trans (sigma.component i) (tau.component (sigma.perm i))

abbrev ActualTensorPacket
    {R : Type uR} [CommSemiring R]
    (C : SourceProcessionCapsuleContract R l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  TensorPacket (C.logShell j) vQ

def Ind1TensorAction
    {R : Type uR} [CommSemiring R]
    (C : SourceProcessionCapsuleContract R l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :
    ActualTensorPacket C j vQ →ₗ[R]
      (⨂[R] i : Capsule j.val,
        ((v : C.place vQ) → (C.logShell j).Shell ((C.polyIso j).labelPerm i) vQ v)) :=
  (C.polyIso j).tensorMap vQ

abbrev FmodUnitCopies (j : Fin (capsuleLevels l)) : Type ua :=
  Capsule j.val -> (I.initial.arithmetic.Fmod)ˣ

def FmodUnitCopy_one (j : Fin (capsuleLevels l)) :
    FmodUnitCopies (I := I) j :=
  fun _ => 1

/-! ## Actual LGP splitting monoid from the source theta packet -/

def thetaLabelOfFin (i : Fin (lStar l.value)) : SignedLabel l.value :=
  ⟨(i.1 : Int), by
    constructor
    · have h0 : (0 : Int) <= (i.1 : Int) := by exact_mod_cast Nat.zero_le i.1
      have hs : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · exact_mod_cast Nat.le_of_lt i.2⟩

def sourceThetaValue (i : Fin (lStar l.value)) : Real :=
  (I.theaterAt 0 0).thetaPacket.scale (thetaLabelOfFin (l := l) i)

def sourceLGPGenerator (i : Fin (lStar l.value)) : Multiplicative Real :=
  Multiplicative.ofAdd (Real.log (sourceThetaValue (I := I) i))

noncomputable def sourceLGPMonoid : SourceLGPMonoidLayer.LGPMonoid l where
  Carrier := Multiplicative Real
  commMonoid := inferInstance
  splittingMonoid := Submonoid.closure (Set.range (sourceLGPGenerator (I := I)))
  thetaValueGenerator := sourceLGPGenerator (I := I)
  splittingMonoid_eq_closure := rfl

def sourceLGPScalar : MonoidHom (Multiplicative Real) Real where
  toFun x := Real.exp x.toAdd
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [Real.exp_add]

noncomputable def sourceLGPActionOn
    {VQ : Type uVQ} {Place : VQ → Type uPlace} {j : Nat}
    (L : LogShellFamily Real Place j) :
    SourceLGPMonoidLayer.LGPMonoidAction (sourceLGPMonoid (I := I)) Real L where
  scalar := sourceLGPScalar

noncomputable def sourceLGPAction (j : Nat) :
    SourceLGPMonoidLayer.LGPMonoidAction (sourceLGPMonoid (I := I)) Real
      (SourceLGPMonoidLayer.standardRealLogShellFamily j) :=
  sourceLGPActionOn (I := I)
    (SourceLGPMonoidLayer.standardRealLogShellFamily j)

end MultiradialProcessionActual
end LeanFormal.IUT.XiFPaper
end
