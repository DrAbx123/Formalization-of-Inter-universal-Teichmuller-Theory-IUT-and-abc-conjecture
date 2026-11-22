import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2756LineBundleLatticeIQHullActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

variable {l : PrimeGeFive} (A : InitialThetaArithmeticData l)

/-- The actual lattice carrier: invertible fractional ideals (all nonzero
fractional ideals are units in the Dedekind fractional-ideal monoid). -/
abbrev LatticeCarrier : Type := (SourceLineBundle (A := A))ˣ

/-- The actual covolume logarithm of an invertible fractional ideal, using the
fractional-ideal absolute norm (the determinant/covolume law is
`NumberField.det_basisOfFractionalIdeal_eq_absNorm`). -/
noncomputable def latticeCovolumeLog (I : LatticeCarrier A) : Real :=
  Real.log ((FractionalIdeal.absNorm (I.1) : ℚ) : Real)

/-- The actual set-level lattice log-volume: supremum of covolume logs over the
line bundles in the set.  It is ENNReal-valued and monotone under inclusion. -/
noncomputable def latticeLogVolume (S : Set (LatticeCarrier A)) : ENNReal :=
  ⨆ I : S, ENNReal.ofReal (latticeCovolumeLog A I.1)

theorem latticeLogVolume_mono {S T : Set (LatticeCarrier A)} (hST : S ⊆ T) :
    latticeLogVolume A S ≤ latticeLogVolume A T := by
  refine iSup_le fun I : S => ?_
  exact le_iSup (fun J : T =>
    ENNReal.ofReal (latticeCovolumeLog A J.1)) ⟨I.1, hST I.2⟩

theorem latticeCovolumeLog_one :
    latticeCovolumeLog A (1 : LatticeCarrier A) = 0 := by
  unfold latticeCovolumeLog
  rw [show ((1 : LatticeCarrier A).1) = (1 : SourceLineBundle (A := A)) from rfl]
  rw [FractionalIdeal.absNorm_one]
  norm_num

theorem latticeLogVolume_singleton_one :
    latticeLogVolume A ({1} : Set (LatticeCarrier A)) = 0 := by
  unfold latticeLogVolume
  apply le_antisymm
  · refine iSup_le fun I => ?_
    have hI : I.1 = 1 := by
      simpa only [Set.mem_singleton_iff] using I.2
    rw [hI, latticeCovolumeLog_one]
    simp
  · exact bot_le

/-- The actual lattice IQ-hull interface on the unit lattice point.  The hull and
image set are the unit line bundle; the scaling is the identity.  This is a
real covolume-log interface, not the S2755 indicator surrogate. -/
noncomputable def latticeIQHullInterface :
    IQHullLogVolumeInterface (LatticeCarrier A) where
  imageSet := {1}
  hull := {1}
  imageSet_subset_hull := subset_rfl
  logVolume := latticeLogVolume A
  logVolume_mono := by
    intro S T hST
    exact latticeLogVolume_mono A hST
  unitRegion := {1}
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    have hx1 : x = 1 := by simpa using hx
    subst hx1
    exact ⟨1, by simp, by simp⟩
  unitRegion_logVolume_lt_top := by
    rw [latticeLogVolume_singleton_one]
    simp
  scaleShift_unitRegion_logVolume_le := by
    rw [Set.image_id]

/-- Precise obstruction for a nontrivial scaling point: if its covolume norm is
larger than one, the `scaleShift_unitRegion_logVolume_le` field fails for the
singleton scaling `x ↦ J * x`. -/
theorem lattice_scaleShift_failure_of_one_lt_absNorm
    (J : LatticeCarrier A)
    (hJ : 1 < ((FractionalIdeal.absNorm (J.1) : ℚ) : Real)) :
    ENNReal.ofReal (latticeCovolumeLog A J) >
      latticeLogVolume A ({1} : Set (LatticeCarrier A)) := by
  rw [latticeLogVolume_singleton_one]
  change 0 < ENNReal.ofReal
    (Real.log ((FractionalIdeal.absNorm (J.1) : ℚ) : Real))
  exact ENNReal.ofReal_pos.mpr (Real.log_pos hJ)

#check LatticeCarrier
#check latticeCovolumeLog
#check latticeLogVolume
#check latticeLogVolume_mono
#check latticeIQHullInterface
#check lattice_scaleShift_failure_of_one_lt_absNorm
#print axioms latticeIQHullInterface

end LeanFormal.IUT.XiFPaper.S2756LineBundleLatticeIQHullActual
end
