import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator

/-!
# Actual analytic theta line bundle and theta section

This file constructs the actual analytic line-bundle model available from the
source theta function on the q-disc.

Base: the actual AnalyticThetaCarrier of Example36SourceThetaGenerator, with
0 < q < 1. Total space: AnalyticThetaCarrier x Complex. Projection is the first
coordinate, with the actual trivialization (Equiv.refl).

The global section is the actual analytic theta value:

  thetaSection t = (t, analyticThetaValue t)

and the zero section is (t, 0). The section is nowhere zero by the actual
theorem analyticThetaValue_ne_zero; hence its zero locus on the q-disc is
empty. This is a genuine analytic trivialized line bundle with the actual theta
function as section.

Important boundary: this is the analytic q-disc trivialization, not a
construction of the source curve theta line bundle or the etale theta function
of IUT II. No automorphy factor, source curve line bundle, or etale theta object
is fabricated here. No inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace ABCBridge.ThetaLineBundleAnalyticActualAdapted

open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor

/-- Actual analytic line bundle over the q-disc with the theta function as
global section. -/
structure AnalyticThetaLineBundle where
  base : Type
  total : Type
  proj : total → base
  trivialization : total ≃ base × ℂ
  trivialization_fst : ∀ x, (trivialization x).1 = proj x
  thetaSection : base → total
  thetaSection_proj : ∀ t, proj (thetaSection t) = t
  zeroSection : base → total
  zeroSection_proj : ∀ t, proj (zeroSection t) = t
  thetaSectionNeZeroSection : ∀ t, thetaSection t ≠ zeroSection t
  zeroLocus : Set base
  zeroLocus_eq : zeroLocus = {t | thetaSection t = zeroSection t}
  zeroLocus_empty : zeroLocus = ∅

/-- The actual analytic theta line bundle on the q-disc. -/
noncomputable def analyticThetaLineBundle : AnalyticThetaLineBundle where
  base := AnalyticThetaCarrier
  total := AnalyticThetaCarrier × ℂ
  proj := Prod.fst
  trivialization := Equiv.refl _
  trivialization_fst := fun _ => rfl
  thetaSection := fun t => (t, analyticThetaValue t)
  thetaSection_proj := fun _ => rfl
  zeroSection := fun t => (t, 0)
  zeroSection_proj := fun _ => rfl
  thetaSectionNeZeroSection := by
    intro t h
    have hsecond : analyticThetaValue t = 0 := by
      exact congrArg Prod.snd h
    exact analyticThetaValue_ne_zero t hsecond
  zeroLocus := {t : AnalyticThetaCarrier | analyticThetaValue t = 0}
  zeroLocus_eq := by
    ext t
    simp only [Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨rfl, h⟩
    · intro h
      exact h.2
  zeroLocus_empty := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact analyticThetaValue_ne_zero t

/-- The actual theta section is nowhere zero. -/
theorem analyticThetaLineBundle_thetaSection_ne_zero
    (t : AnalyticThetaCarrier) :
    (analyticThetaLineBundle.thetaSection t : AnalyticThetaCarrier × ℂ) ≠
      analyticThetaLineBundle.zeroSection t :=
  analyticThetaLineBundle.thetaSectionNeZeroSection t

/-- The actual theta section projects to its base point. -/
theorem analyticThetaLineBundle_thetaSection_proj
    (t : AnalyticThetaCarrier) :
    analyticThetaLineBundle.proj (analyticThetaLineBundle.thetaSection t) = t :=
  analyticThetaLineBundle.thetaSection_proj t

/-- The actual zero locus of the analytic theta section is empty. -/
theorem analyticThetaLineBundle_zeroLocus_empty :
    analyticThetaLineBundle.zeroLocus = ∅ :=
  analyticThetaLineBundle.zeroLocus_empty

/-- The actual analytic theta value is the fiber coordinate of the theta section
under the trivialization. -/
theorem analyticThetaLineBundle_section_fst
    (t : AnalyticThetaCarrier) :
    (analyticThetaLineBundle.trivialization
      (analyticThetaLineBundle.thetaSection t)).2 = analyticThetaValue t :=
  rfl

end ABCBridge.ThetaLineBundleAnalyticActualAdapted

end
