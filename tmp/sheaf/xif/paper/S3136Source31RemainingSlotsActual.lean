import tmp.sheaf.xif.paper.S3136Source31AssemblyConditionalActual

/-! # Stage-4 host: remaining SourceDefinition31Data slots and compatibility pairs

Source anchor: IUT I, Definition 3.1 (torsion, orbicurve, sections, cusp clauses and
the five arithmetic-compatibility pairs).

CONSUMER: qpilot's modelSourceDefinition31Data assembly. This file gives explicit DATA
records for the four remaining clause slots and the five compatibility pairs, and
composes them with the native reduction-clause provider (S3136Source31AssemblyConditional
Actual) into the complete Definition 3.1 source contract. Nothing is faked: each slot is
a real data field and every compatibility pair carries its own Prop and proof.

LABEL: conditional assembly component. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136Source31RemainingSlotsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual
open LeanFormal.IUT.XiFPaper.S3136Source31AssemblyConditionalActual

variable {l : PrimeGeFive}

/-- The four remaining clause slots of the Definition 3.1 source contract. -/
structure LGPModelRemainingSlots (l : PrimeGeFive) where
  torsion : SourceTorsionClause l
  orbicurve : SourceOrbicurveClause
  sections : SourceSectionClause
  cusp : SourceCuspClause

/-- The five arithmetic-compatibility pairs. -/
structure LGPModelCompatPairs where
  c_red : Prop
  h_red : c_red
  c_tor : Prop
  h_tor : c_tor
  c_orb : Prop
  h_orb : c_orb
  c_sec : Prop
  h_sec : c_sec
  c_cusp : Prop
  h_cusp : c_cusp

variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Complete conditional assembly: native datum + split-input family (reduction slot) +
remaining clause data + compatibility pairs -> Definition 3.1 source contract. -/
def lgpSource31Data_full
    (F : NativeSplitInputFamily (l := l) T)
    (R : LGPModelRemainingSlots l)
    (C : LGPModelCompatPairs) :
    SourceDefinition31Data l :=
  lgpSource31Data_native (l := l) T F R.torsion R.orbicurve R.sections R.cusp
    C.c_red C.h_red C.c_tor C.h_tor C.c_orb C.h_orb C.c_sec C.h_sec C.c_cusp C.h_cusp

/-- The complete assembly has the native datum arithmetic. -/
theorem lgpSource31Data_full_arithmetic
    (F : NativeSplitInputFamily (l := l) T)
    (R : LGPModelRemainingSlots l)
    (C : LGPModelCompatPairs) :
    (lgpSource31Data_full (l := l) T F R C).arithmetic = T.arithmetic := rfl

#check LGPModelRemainingSlots
#check LGPModelCompatPairs
#check lgpSource31Data_full
#check lgpSource31Data_full_arithmetic

end LeanFormal.IUT.XiFPaper.S3136Source31RemainingSlotsActual
end