import tmp.sheaf.xif.paper.Hull11H6Mzk1UpgradeActual
import tmp.sheaf.xif.paper.Mzk1GeomCorePreciseToOldActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: Hull11 H6 upgrade|precise GeometricCore witness|toOldRecast -> hits Hull11H6Mzk1UpgradeActual:61-86 (HullH6UpgradeInputs/hull11_h6_upgrade with old Mzk1GeometricCoreRecast), Mzk1GeomCorePreciseToOldActual:58-108 (toOldWitness/toOldRecast precise->old) -> ADAPT (precise witness version of the Hull11 consumer; no closure).

# Hull11PreciseConsumerActual — Hull11 H6 consumer with the PRECISE GeometricCore witness

Replaces the old (free-Prop) Mzk1GeometricCoreRecast input of Hull11 by the precise
schema Mzk1GeometricCoreRecastPrecise, converting field-wise via toOldRecast, and
re-establishes the full Hull11 conclusion (Cor 3.12 + H6 GenEll transfer + Mzk1 Thm
2.5 witness conclusion).  Named inputs (2.2/2.4/precise GeometricCore existence)
stay explicit; no closure.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull11PreciseConsumerActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual
open LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual
open LeanFormal.IUT.XiFPaper.GenEll10bH6Mzk1WiringActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCorePreciseToOldActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual
open LeanFormal.IUT.XiFPaper.Hull11H6Mzk1UpgradeActual
open NeronModelInfra
open CategoryTheory AlgebraicGeometry

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- H6 upgrade inputs with the PRECISE GeometricCore witness schema instead of the
old free-Prop recast. -/
structure HullH6PreciseUpgradeInputs (Point : Type u) {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  hull : HullDetAssemblyInputs M
  shadow : AdaptedIVGenEllShadow Point
  h22 : Lemma22FullStatementShape
  h24 : Lemma24Shape.{u}
  hcore : Mzk1GeometricCoreRecastPrecise c ε T D

/-- Convert the precise-input record to the old Hull11 input record (field-wise
precise->old witness conversion via `toOldRecast`). -/
def HullH6PreciseUpgradeInputs.toOldInputs (Point : Type u) {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (In : HullH6PreciseUpgradeInputs (l := l) M Point c ε T D) :
    HullH6UpgradeInputs (l := l) M Point c ε T D :=
  { hull := In.hull
    shadow := In.shadow
    h22 := In.h22
    h24 := In.h24
    hcore := toOldRecast In.hcore }

/-- **H6 upgrade consumer (precise witness version):** from the hull+det assembly,
the GenEll shadow, the named 2.2/2.4 inputs and the PRECISE GeometricCore recast,
get the Cor 3.12 hull+det conclusion, the H6 GenEll transfer and the Mzk1 Thm 2.5
witness conclusion.  All inputs are consumed; named inputs stay named (no closure). -/
theorem hull11_h6_upgrade_precise (Point : Type u) {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (In : HullH6PreciseUpgradeInputs (l := l) M Point c ε T D) :
    Cor312HullDetConclusion M In.hull.theta ∧
      (∃ lowerBound : ℝ, ∀ x : Point,
        lowerBound ≤ (1 + In.shadow.epsilon) *
          (In.shadow.logDiff x + In.shadow.logCond x) - In.shadow.height x) ∧
      (∃ W : Mzk1GeometricCoreWitness c ε T D,
        Mzk1Thm25Conclusion c ε T D W) :=
  hull11_h6_upgrade (M := M) Point c ε T D
    (In.toOldInputs (l := l) M Point c ε T D)

/-- The precise witness yields the old witness (Nonempty projection). -/
theorem hull11_precise_witness_nonempty (Point : Type u) {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (In : HullH6PreciseUpgradeInputs (l := l) M Point c ε T D) :
    Nonempty (Mzk1GeometricCoreWitness c ε T D) :=
  In.hcore.elim fun w => ⟨toOldWitness w⟩

/-- Row record: precise-witness upgrade vs remaining named inputs. -/
def hull11PreciseRows : List (String × String × String) :=
  [ ("Hull11 H6 consumer with precise GeometricCore witness", "A", "PROVED hull11_h6_upgrade_precise (toOldRecast conversion)")
  , ("precise witness -> old witness inside the consumer", "A", "PROVED hull11_precise_witness_nonempty (toOldWitness)")
  , ("full Lemma 2.2 StatementShape", "B", "NAMED (stage4 induction)")
  , ("Lemma 2.4 shape", "B", "NAMED (stage4/mainline 2.4)")
  , ("precise GeometricCore witness existence", "B", "NAMED class-B (GenEll15GeometricCoreStatementPrecise)") ]

theorem hull11PreciseRows_length : hull11PreciseRows.length = 5 := rfl

#check HullH6PreciseUpgradeInputs
#check HullH6PreciseUpgradeInputs.toOldInputs
#check hull11_h6_upgrade_precise
#check hull11_precise_witness_nonempty
#check hull11PreciseRows_length

end LeanFormal.IUT.XiFPaper.Hull11PreciseConsumerActual
end