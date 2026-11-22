import LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerH1H2BridgeActual — A476 real consumer theorems (DTheta bridge / H2 package)

New conclusions combining existing donor theorems from
\`SourceH1H2Construction.lean\`:

* \`dTheta_bridge_package\` (:131/134/145/151/155/159): for each family index
  the bridge's F-strip recovery, D-strip recovery, arrow-is-refl and
  arrow-compatibility hold jointly;
* \`h2_package_consumer\` (:2317/2320/2323/2326/2329/2365): the H2 package's
  h1/fProcession/dProcession/permutation projections, the F->D procession
  compatibility and the source-closure equality hold jointly.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerH1H2BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/-- **DTheta bridge package consumer** (per family index). -/
theorem dTheta_bridge_package {l : PrimeGeFive} {V : Type*}
    (I : Theorem311Source.OriginalInput l V) (i : I.family.index) :
    I.bridge.fStrip i = (I.family.theater i).primeStrip ∧
      I.bridge.dStrip i = (I.bridge.fStrip i).toD ∧
      I.bridge.arrow i = DPrimeStripEquiv.refl (I.bridge.dStrip i) ∧
      (∀ (v : V) (x : (I.bridge.dStrip i).Pi v),
        (I.bridge.fStrip i).toD.proj v ((I.bridge.arrow i).isoPi v x) =
          (I.bridge.arrow i).isoG v ((I.bridge.dStrip i).proj v x)) :=
  ⟨I.bridge_source_recovery i, I.bridge_d_recovery i, I.bridge_arrow_is_refl i,
   fun v x => I.bridge_arrow_compatibility i v x⟩

/-- **H2 construction package consumer** (six joint equalities). -/
theorem h2_package_consumer {l : PrimeGeFive} {V : Type*}
    (I : Theorem311Source.OriginalInput l V)
    (P : Theorem311Source.H2SpokePermutation I) :
    (I.h2Package P).h1 = I.h1 ∧
      (I.h2Package P).fProcession = Theorem311Source.H2FProcession.canonical (I := I) ∧
      (I.h2Package P).dProcession = Theorem311Source.H2DProcession.canonical (I := I) ∧
      (I.h2Package P).permutation = P ∧
      (I.h2Package P).fProcession.toD = (I.h2Package P).dProcession ∧
      (I.h2Package P).h1.source = I.initial :=
  ⟨I.h2Package_h1 P, I.h2Package_fProcession P, I.h2Package_dProcession P,
   I.h2Package_permutation P, I.h2Package_procession_toD P,
   (I.h1_h2_source_closed P).1⟩

#check dTheta_bridge_package
#check h2_package_consumer

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerH1H2BridgeActual
end