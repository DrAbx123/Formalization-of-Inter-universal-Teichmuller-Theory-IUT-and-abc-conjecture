import tmp.sheaf.xif.paper.PaperThetaHullThenAverageActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-! # Product-carrier hull identity inflation and actual lambda-O fallback

On the product paper carrier

  PaperThetaPilotPoint = F_l^x -> Multiplicative Real,

the generic value-realized hull holomorphicHull is a least submonoid stable
under the scaling units.  Every submonoid contains the identity.  Hence every
paperLabelHull q j contains the unit point 1, independently of the theta
possible image.  This is an identity/unit-region inflation: the signed hull
log-volume is not the local theta log scalar and can look trivial.

The paper hull is a least lambda-O region, not a submonoid.  On the actual C3
log-shell tensor block the actual lambda-O scaling and actual unit region are
available (actualScaledRegion, actualUnitRegion); this file constructs the
actual nontrivial lambda-O hull scalar there:

  nontrivialC3LambdaOHullScalar lam
    = (actualC3LogShellTensorHaar (actualScaledRegion lam)).toReal.

The product carrier itself has no constructed actual compact unit region O with
positive finite Haar; that is recorded as the exact missing data, not faked.

No zero/trivial direction, no fake inequality, no sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaHullUnitInflationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaHullThenAverageActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

universe u ua uv upi umon ui

variable {l : PrimeGeFive}
variable (q : Real)

/-- The generic product-carrier per-label hull contains the identity. -/
theorem one_mem_paperLabelHull (j : ProcessionLabel l) :
    (1 : PaperThetaPilotPoint (l := l)) ∈
      paperLabelHull (l := l) q j :=
  (paperLabelHull (l := l) q j).one_mem

/-- Exact identity-inflation statement for the product hull. -/
def PaperProductHullContainsIdentity : Prop :=
  forall j : ProcessionLabel l,
    (1 : PaperThetaPilotPoint (l := l)) ∈ paperLabelHull (l := l) q j

theorem paperProductHullContainsIdentity_holds :
    PaperProductHullContainsIdentity (l := l) q :=
  fun j => one_mem_paperLabelHull (l := l) q j

/-- Exact missing product-carrier unit region data: an actual O on the product
carrier with the unit point, compactness, and positive finite Haar. -/
structure PaperProductUnitRegionData where
  unitRegion : Set (PaperThetaPilotPoint (l := l))
  one_mem : (1 : PaperThetaPilotPoint (l := l)) ∈ unitRegion
  unitRegion_compact : IsCompact unitRegion
  unitRegion_measure_pos : 0 < paperThetaPilotHaar (l := l) unitRegion
  unitRegion_measure_lt_top : paperThetaPilotHaar (l := l) unitRegion < ⊤

/-- The exact product-carrier unit-region requirement; no inhabitant is
asserted. -/
def PaperProductUnitRegionRequired : Prop :=
  Nonempty (PaperProductUnitRegionData (l := l))

/-- Actual nontrivial lambda-O hull scalar on the C3 log-shell tensor block,
using the actual unit region and actual lambda-scaling. -/
noncomputable def nontrivialC3LambdaOHullScalar
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (lam : HullBlock C3) : Real :=
  (actualC3LogShellTensorHaar C3
    (actualScaledRegion C3 lam)).toReal

/-- The actual lambda-O region is exactly a scaling of the actual C3 unit
region. -/
theorem nontrivialC3LambdaOHullScalar_eq
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (lam : HullBlock C3) :
    nontrivialC3LambdaOHullScalar (l := l) C3 lam =
      (actualC3LogShellTensorHaar C3
        (actualScaledRegion C3 lam)).toReal := rfl

end LeanFormal.IUT.XiFPaper.PaperThetaHullUnitInflationActual

end
