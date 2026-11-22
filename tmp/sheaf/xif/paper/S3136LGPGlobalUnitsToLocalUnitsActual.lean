import tmp.sheaf.xif.paper.S3136LGPLocalTensorPacketActual

/-! # Stage-4 host: global units -> local units at C3 tensor places (component)

Source anchors: IUT III, pp. 616-620 and Fig. I.5 (local-unit/Frobenius
interface at prime-strip fibers); IUT I, Definition 3.1.

This file exposes the actual GLOBAL-UNITS -> LOCAL-UNITS maps at the C3 tensor
places, built from the actual algebra structure of the completions (no
reciprocity input):
* lgpGlobalUnitsToLocalUnits C3 i: (Fmod)^x ->* (Completion (c3LogShellPlace))^x;
* lgpC3Fiber_eq_completion: the actual packet fiber type is this completion;
* lgpGlobalUnitsToLocalUnits_apply: value formula (Units.map of algebraMap);
* LGPGlobalUnitsLocalMissing/Gap: exact remaining data (same-C identification
  F ~ Fmod, V -> C3 tensor-index place selection, Frobenius compatibility;
  refs above), no contract change, no reciprocity assumed.

LABEL: prerequisite component only.  Named consumer: stepxi task-55 C2
finite-copy action; lattice R1/R-A. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPGlobalUnitsToLocalUnitsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual packet fiber is the actual completion at the selected place. -/
theorem lgpC3Fiber_eq_completion (i : C3.tensorIndex) :
    C3LogShellFiber C3 i = Completion (c3LogShellPlace C3 i).val := rfl

/-- The actual global-units -> local-units map at the selected C3 tensor place. -/
noncomputable def lgpGlobalUnitsToLocalUnits (i : C3.tensorIndex) :
    (I.initial.arithmetic.Fmod)ˣ →* (Completion (c3LogShellPlace C3 i).val)ˣ :=
  Units.map (algebraMap (I.initial.arithmetic.Fmod)
    (Completion (c3LogShellPlace C3 i).val)).toMonoidHom

/-- The value formula: the map is Units.map of the actual algebraMap. -/
theorem lgpGlobalUnitsToLocalUnits_apply (i : C3.tensorIndex)
    (u : (I.initial.arithmetic.Fmod)ˣ) :
    ((lgpGlobalUnitsToLocalUnits C3 i u :
        (Completion (c3LogShellPlace C3 i).val)ˣ) :
        Completion (c3LogShellPlace C3 i).val) =
      algebraMap (I.initial.arithmetic.Fmod)
        (Completion (c3LogShellPlace C3 i).val)
        (u : I.initial.arithmetic.Fmod) := rfl

/-- Exact missing data for the first-triangle local-unit interface (IUT III,
pp. 616-620, Fig. I.5):
* sameCIdentification: the same-C identification F ~ Fmod (arithmetic model map
  M0), needed to feed the map from the actual T.arithmetic.F units;
* placeSelection: the V -> C3 tensor-index place selection (the c3LogShellPlace
  data; M1 index equivalence), needed to index the local fibers by V;
* frobeniusCompatibility: compatibility with the local Frobenius actions and
  the LGP splitting monoid of the local units;
* reciprocalImageCompatibility: the reciprocal-image/Theta-link compatibility
  of the local units. -/
structure LGPGlobalUnitsLocalMissing where
  sameCIdentification : Prop
  placeSelection : Prop
  frobeniusCompatibility : Prop
  reciprocalImageCompatibility : Prop

/-- The exact global-units/local-units gap. -/
def LGPGlobalUnitsLocalGap : Prop :=
  Nonempty LGPGlobalUnitsLocalMissing

#check lgpC3Fiber_eq_completion
#check lgpGlobalUnitsToLocalUnits
#check lgpGlobalUnitsToLocalUnits_apply
#check LGPGlobalUnitsLocalGap

end LeanFormal.IUT.XiFPaper.S3136LGPGlobalUnitsToLocalUnitsActual
end