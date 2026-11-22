import tmp.sheaf.xif.paper.S1221StripOfChoiceActual

/-! # S1225: actual source-choice operations and the first exact Core/Profile gap

Choice = I.family.index.  The actual index shifts give permutation operations
ind1/ind2/ind3.  The profile logVolume is the actual theater thetaPacket.logVolume.
The first exact datum needed to assemble a Carrier/Profile is the invariance of
that logVolume under the shifts; it is not supplied by the source input.
No weak wrapper is written. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev Choice : Type _ := I.family.index

/-- Actual horizontal index permutation. -/
noncomputable def horizontalPerm : Equiv.Perm (Choice (I := I)) where
  toFun := I.horizontalShift
  invFun := I.horizontalShiftInv
  left_inv := I.horizontalShiftInv_left
  right_inv := I.horizontalShiftInv_right

/-- Actual vertical index permutation. -/
noncomputable def verticalPerm : Equiv.Perm (Choice (I := I)) where
  toFun := I.verticalShift
  invFun := I.verticalShiftInv
  left_inv := I.verticalShiftInv_left
  right_inv := I.verticalShiftInv_right

/-- Actual Ind1 operation: inverse horizontal permutation power. -/
noncomputable def sourceInd1 (g : ℤ) (c : Choice (I := I)) : Choice (I := I) :=
  ((horizontalPerm (I := I)) ^ (-g)) c

/-- Actual Ind2 operation: inverse vertical permutation power. -/
noncomputable def sourceInd2 (g : ℤ) (c : Choice (I := I)) : Choice (I := I) :=
  ((verticalPerm (I := I)) ^ (-g)) c

/-- Actual Ind3 operation: the actual translate (n,0) permutation. -/
noncomputable def translatePerm (n : ℤ) : Equiv.Perm (Choice (I := I)) where
  toFun := I.translate n 0
  invFun := I.translateInv n 0
  left_inv := I.translateInv_left n 0
  right_inv := I.translateInv_right n 0

noncomputable def sourceInd3 (n : Nat) (c : Choice (I := I)) : Choice (I := I) :=
  ((translatePerm (I := I) (n : ℤ))) c

/-- Actual profile logVolume: the theater thetaPacket log-volume. -/
noncomputable def sourceLogVolume (c : Choice (I := I)) : Real :=
  (I.family.theater c).thetaPacket.logVolume

/-- First exact Core/Profile gap: logVolume invariance/upper under the actual
shifts.  No inhabitant is asserted. -/
def S1225LogVolumeShiftLaws : Prop :=
  (∀ (g : ℤ) (c : Choice (I := I)),
    sourceLogVolume (I := I) (sourceInd1 (I := I) g c) =
      sourceLogVolume (I := I) c) ∧
  (∀ (g : ℤ) (c : Choice (I := I)),
    sourceLogVolume (I := I) (sourceInd2 (I := I) g c) =
      sourceLogVolume (I := I) c) ∧
  (∀ (n : Nat) (c : Choice (I := I)),
    sourceLogVolume (I := I) c ≤
      sourceLogVolume (I := I) (sourceInd3 (I := I) n c))

/-- Exact first field needed before Carrier/Profile/SourceRun on Choice=I.family.index. -/
def S1225FirstExactField : Prop :=
  S1225LogVolumeShiftLaws (I := I)

end LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual
end