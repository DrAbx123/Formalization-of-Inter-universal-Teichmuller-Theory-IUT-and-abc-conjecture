import LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2CardReduction
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullInterfaceDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerKummerIdentityHullCompactActual — A476 consumer theorems

New conclusions combining existing donor theorems:

* labelled Kummer identity (\`SourceK1K2CardReduction.lean:55/63/66\`):
  the identity iso's map law, inverse law and constant-label law jointly;
* hull compactness (\`SourceHullCompactnessReduction.lean:88/95/104\`):
  image-volume monotonicity, the transferred lower bound and finiteness
  jointly, and a chain with the real-representation theorem
  (\`SourceHullInterfaceDischarge.lean:85\`) giving the representation
  together with finiteness.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerKummerIdentityHullCompactActual

open LeanFormal.IUT

/-- **Labelled Kummer identity package consumer** (map, inverse, label). -/
theorem labelledKummerIdentity_package (Choice : Type*) :
    (∀ a : Choice, (labelledKummerIdentity Choice).map a = a) ∧
      (∀ b : Choice, (labelledKummerIdentity Choice).inverse b = b) ∧
      (∀ c : Choice, (labelledKummerIdentity Choice).label c = 0) :=
  ⟨labelledKummerIdentity_map Choice,
   labelledKummerIdentity_inverse Choice,
   fun _ => rfl⟩

/-- **Hull compactness package consumer**: image-volume monotonicity, lower-bound
transfer and finiteness jointly. -/
theorem hull_compact_finiteness_package {X : Type*} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    W.logVolume W.imageSet ≤ W.logVolume W.hull ∧
      lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨IQHullLogVolumeInterface.imageSet_logVolume_le_hull W,
   (IQHullLogVolumeInterface.lower_bound_and_finiteness W h).1,
   (IQHullLogVolumeInterface.lower_bound_and_finiteness W h).2⟩

/-- **Hull compactness + real representation chain consumer**. -/
theorem hull_compact_representation_chain {X : Type*} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    (∃ M : Real, W.logVolume W.hull = ENNReal.ofReal M ∧
        lowerBound ≤ ENNReal.ofReal M) ∧
      W.logVolume W.hull < ⊤ :=
  ⟨IQHullLogVolumeInterface.hull_logVolume_realRepresentation W h,
   IQHullLogVolumeInterface.hull_logVolume_lt_top W⟩

#check labelledKummerIdentity_package
#check hull_compact_finiteness_package

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerKummerIdentityHullCompactActual
end