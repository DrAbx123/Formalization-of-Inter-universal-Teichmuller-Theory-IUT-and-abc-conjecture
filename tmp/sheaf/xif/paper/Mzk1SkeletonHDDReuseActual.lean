import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1238HDDLocalLatticeExactFirstField
import tmp.sheaf.xif.paper.Mzk1HDDObjectAdaptedActual

/-!
# Mzk1SkeletonHDDReuseActual — iut-skeleton HDD node reuse from existing HDD/SHE assets

Lead A475 reuse rule: exhaustive search found existing assets
(1) Mzk1HDDObjectActual (HDD/HDDDecomposition; no olean -> adapted copy
    Mzk1HDDObjectAdaptedActual.lean, compiled as new file);
(2) S1215SourceSHEHDDCompatibilityActual.lean (EXIT0/olean; SHE<->HDD compatibility);
(3) S1238HDDLocalLatticeExactFirstField.lean (EXIT0/olean; HDD local-lattice first field);
(4) S1154HDDPreauditActual.lean (olean; preaudit).
This file bundles/aliases them for the iut-skeleton HDD node; no new theory.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SkeletonHDDReuseActual

open LeanFormal.IUT

/-- Existing Shear/HDD compatibility (S1215 asset). -/
def sourceSHEHDDCompatibilityReuse :=
  @SourceSHEHDDCompatibility

/-- Existing S1215 log-shift/readout compatibility (tree-tmp asset). -/
def s1215LogShiftReadoutReuse :=
  @s1215LogShiftReadoutCompat_actual

/-- Existing S1238 HDD local-lattice type (asset). -/
abbrev s1238HDDLocalLatticeTypeReuse :=
  S1238HDDLocalLatticeType

/-- The HDD object from the adapted existing asset. -/
def hddObjectReuse :=
  @LeanFormal.IUT.XiFPaper.Mzk1HDDObjectAdaptedActual.HDD

/-- Skeleton HDD reuse rows: (skeleton node, existing asset, status). -/
def skeletonHDDReuseRows : List (String × String × String) :=
  [ ("iut-skeleton:HDD", "Mzk1HDDObjectActual (adapted copy registered)", "REUSE (adapted file)"),
    ("SHE<->HDD compatibility", "S1215SourceSHEHDDCompatibilityActual (olean)", "REUSE (existing asset)"),
    ("HDD local-lattice first field", "S1238HDDLocalLatticeExactFirstField (olean)", "REUSE (existing asset)"),
    ("HDD preaudit", "S1154HDDPreauditActual (olean)", "REUSE (existing asset)"),
    ("full HDD paper object", "not asserted", "NAMED") ]

/-- The skeleton HDD reuse row record has five rows. -/
theorem skeletonHDDReuseRows_length : skeletonHDDReuseRows.length = 5 := rfl

#check sourceSHEHDDCompatibilityReuse
#check s1215LogShiftReadoutReuse
#check s1238HDDLocalLatticeTypeReuse
#check hddObjectReuse
#check skeletonHDDReuseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SkeletonHDDReuseActual
end
