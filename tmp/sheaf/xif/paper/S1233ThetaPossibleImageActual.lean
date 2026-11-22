import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily

/-! # S1233: theta possible image on I.family.index

Constructs the actual allowed-image set from the source theta packet scales:

```text
thetaPossibleImage I i := { Real.log ((I.family.theater i).thetaPacket.scale j)
                           | j : SignedLabel l.value }
```

The family link proves this set is independent of `i`, and we prove the four
`ProcessionPacketProfile.possibleImage` laws for an arbitrary procession
structure on `I.family.index`.  This does not construct the profile's
logVolume or its Ind volume laws; those remain separate. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1233ThetaPossibleImageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- A concrete theta label: zero lies in the signed interval. -/
noncomputable def thetaLabelZero : SignedLabel l.value :=
  ⟨0, by
    rw [Set.mem_Icc]
    constructor
    · have h : (0 : Int) ≤ (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · have h : (0 : Int) ≤ (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
  ⟩

/-- Actual theta possible image at a source index: logs of the theta packet
scales. -/
noncomputable def thetaPossibleImage (i : I.family.index) : Set Real :=
  Set.range (fun j : SignedLabel l.value =>
    Real.log ((I.family.theater i).thetaPacket.scale j))

theorem thetaPossibleImage_nonempty (i : I.family.index) :
    (thetaPossibleImage I i).Nonempty := by
  refine ⟨Real.log ((I.family.theater i).thetaPacket.scale
    (thetaLabelZero (l := l))), ?_⟩
  exact ⟨thetaLabelZero (l := l), rfl⟩

/-- The actual theta possible image is independent of the source index: the
family links identify all theta packet scales. -/
theorem thetaPossibleImage_eq (i j : I.family.index) :
    thetaPossibleImage I i = thetaPossibleImage I j := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    change Real.log ((I.family.theater j).thetaPacket.scale k) =
      Real.log ((I.family.theater i).thetaPacket.scale k)
    rw [I.family.link_scale i j k]
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    change Real.log ((I.family.theater i).thetaPacket.scale k) =
      Real.log ((I.family.theater j).thetaPacket.scale k)
    rw [I.family.link_scale_symm i j k]

variable {Label : Type uLabel} [AddGroup Label]
variable (P : DPrimeStripProcession Label I.family.index)

theorem thetaPossibleImage_ind1 (g : Label) (c : I.family.index) :
    thetaPossibleImage I (P.ind1 g c) = thetaPossibleImage I c :=
  thetaPossibleImage_eq I _ _

theorem thetaPossibleImage_ind2 (g : Label) (c : I.family.index) :
    thetaPossibleImage I (P.ind2 g c) = thetaPossibleImage I c :=
  thetaPossibleImage_eq I _ _

theorem thetaPossibleImage_ind3 (n : Nat) (c : I.family.index) (z : Real)
    (hz : z ∈ thetaPossibleImage I c) :
    ∃ w, w ∈ thetaPossibleImage I (P.ind3 n c) ∧ z ≤ w := by
  refine ⟨z, ?_, le_rfl⟩
  simpa [thetaPossibleImage_eq I (P.ind3 n c) c] using hz

#check thetaPossibleImage
#check thetaPossibleImage_nonempty
#check thetaPossibleImage_eq
#check thetaPossibleImage_ind1
#check thetaPossibleImage_ind2
#check thetaPossibleImage_ind3

end LeanFormal.IUT.XiFPaper.S1233ThetaPossibleImageActual
end
