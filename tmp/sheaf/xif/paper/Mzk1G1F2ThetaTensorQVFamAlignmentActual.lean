/- R3/Θ-data alignment: fill `ThetaTensorQVFamAlignment` from the ACTUAL qVFamily coefficients.

  `ThetaTensorQVFamAlignment T` (ThetaTensorScaledImageActual.lean:91) has the single field
  `coefficients : SignedLabel l.value → ι → Real`. Taking `ι := Bad (nativePlaceSelection T)`
  the actual K-side theta coefficients are
  `(gaussExponent j.1).toNat * actualRootCoeff T b ()`; this gives a genuine inhabitant,
  so `ThetaTensorQVFamAlignmentObstruction` is DISCHARGED for the Bad-indexed packet.
  The remaining alignment to a SPECIFIC tensor place/tuple (places : ι → V → ...) is the
  K-side place transport already recorded separately; here only the coefficients are filled
  (the structure has exactly that field). No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTensorQVFamAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive}

/-- **实际 qVFamily 系数填充 alignment**：`ι := Bad (nativePlaceSelection T)`。 -/
noncomputable def thetaTensorQVFamAlignmentOfActual
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    ThetaTensorQVFamAlignment (ι := Bad (nativePlaceSelection T)) (l := l) T where
  coefficients := fun j b => ((gaussExponent j.1).toNat : ℝ) * actualRootCoeff (l := l) T b ()

/-- **障碍解除**：Bad-indexed packet 的 alignment 非空。 -/
theorem thetaTensorQVFamAlignmentObstruction_actual
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    ThetaTensorQVFamAlignmentObstruction (ι := Bad (nativePlaceSelection T)) (l := l) T :=
  ⟨thetaTensorQVFamAlignmentOfActual (l := l) T⟩

#print axioms thetaTensorQVFamAlignmentObstruction_actual

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTensorQVFamAlignmentActual