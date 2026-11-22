import tmp.sheaf.xif.paper.S3136LGPLocalMonoidActual

/-! # Stage-4 host: global units -> bad-place local units (component)

Source anchors: IUT III, pp. 616-620, Fig. I.5; IUT II, Remark 2.5.1, (i).

Actual global-units -> bad-place-local-units maps at the bad (native) places,
built from the actual algebra structure of the completions (no reciprocity),
together with the composite into the algebraic closure where the theta values
live:
* lgpGlobalUnitsToBadPlaceUnits b: (T.arithmetic.F)^x ->* (Completion (qVPlace T b))^x;
* lgpGlobalUnitsToBadPlaceAlgClosed b: the composite into the algebraic-closure
  unit group;
* value formula;
* LGPBadPlaceUnitsMissing/Gap: exact remaining data (same-C identification,
  Frobenius/splitting compatibility, reciprocal-image compatibility).

LABEL: prerequisite component only.  Consumer: stepxi task-55 C2, lattice R1. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPGlobalUnitsToBadPlaceUnitsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalMonoidActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global-units -> bad-place-local-units map. -/
noncomputable def lgpGlobalUnitsToBadPlaceUnits
    (b : Bad (nativePlaceSelection T)) :
    (T.arithmetic.F)ˣ →* (Completion (qVPlace T b))ˣ :=
  Units.map (algebraMap (T.arithmetic.F) (Completion (qVPlace T b))).toMonoidHom

/-- The composite into the algebraic-closure unit group (actual units). -/
noncomputable def lgpGlobalUnitsToBadPlaceAlgClosed
    (b : Bad (nativePlaceSelection T)) :
    (T.arithmetic.F)ˣ →*
      (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  (Units.map (algebraMap (Completion (qVPlace T b))
    (AlgebraicClosure (Completion (qVPlace T b)))).toMonoidHom).comp
      (lgpGlobalUnitsToBadPlaceUnits T b)

/-- Value formula for the bad-place map. -/
theorem lgpGlobalUnitsToBadPlaceUnits_apply
    (b : Bad (nativePlaceSelection T)) (u : (T.arithmetic.F)ˣ) :
    ((lgpGlobalUnitsToBadPlaceUnits T b u : (Completion (qVPlace T b))ˣ) :
        Completion (qVPlace T b)) =
      algebraMap (T.arithmetic.F) (Completion (qVPlace T b))
        (u : T.arithmetic.F) := rfl

/-- Exact missing data for the bad-place local-unit interface: same-C
identification, Frobenius/splitting compatibility, reciprocal-image
compatibility (IUT III, pp. 616-620, Fig. I.5; IUT II, Remark 2.5.1(i)). -/
structure LGPBadPlaceUnitsMissing where
  sameCIdentification : Prop
  frobeniusSplittingCompatibility : Prop
  reciprocalImageCompatibility : Prop

/-- The exact bad-place local-unit gap. -/
def LGPBadPlaceUnitsGap : Prop := Nonempty LGPBadPlaceUnitsMissing

#check lgpGlobalUnitsToBadPlaceUnits
#check lgpGlobalUnitsToBadPlaceAlgClosed
#check lgpGlobalUnitsToBadPlaceUnits_apply
#check LGPBadPlaceUnitsGap

end LeanFormal.IUT.XiFPaper.S3136LGPGlobalUnitsToBadPlaceUnitsActual
end