/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.external.ported.flt.FLT.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# P1: IdealLocalizedCount via FLT completionIdeal + uniformizer (3 bridges)
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual
open LeanFormal.IUT.NumberFieldFinitePlace
open Multiplicative

variable {k : Type} [Field k] [NumberField k]

def completionIdealOf (v : NumberField.FinitePlace k) :
    Ideal (LocalRing (k := k) v) :=
  IsDedekindDomain.HeightOneSpectrum.completionIdeal k (underlyingPrime v)

def IdealMapPowerStatement (I : Ideal (NumberField.RingOfIntegers k)) (_hI : I ≠ 0)
    (v : NumberField.FinitePlace k) : Prop :=
  Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v)) I =
    (completionIdealOf (k := k) v) ^
      ((Associates.mk (underlyingPrime v).asIdeal).count (Associates.mk I).factors)

def LocalizedLineIdealMapStatement (I : Ideal (NumberField.RingOfIntegers k))
    (_hI : I ≠ 0) (v : NumberField.FinitePlace k) : Prop :=
  localizedLine (k := k) (I : LineBundle (k := k)) v =
    Submodule.span (LocalRing (k := k) v)
      ((fun x : LocalRing (k := k) v => (x : LocalField (k := k) v)) ''
        ((Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v)) I :
          Ideal (LocalRing (k := k) v)) : Set (LocalRing (k := k) v)))

def UniformizerPowerSpanStatement (v : NumberField.FinitePlace k) : Prop :=
  forall (pi : LocalRing (k := k) v),
    Valued.v (pi : LocalField (k := k) v) = ofAdd (-1 : Int) ->
    forall e : Nat,
      Submodule.span (LocalRing (k := k) v)
        ((fun x : LocalRing (k := k) v => (x : LocalField (k := k) v)) ''
          (((completionIdealOf (k := k) v) ^ e : Ideal (LocalRing (k := k) v)) :
            Set (LocalRing (k := k) v))) =
        Submodule.span (LocalRing (k := k) v)
          {((pi : LocalField (k := k) v) ^ e)}

theorem idealLocalizedCount_of_bridges (I : Ideal (NumberField.RingOfIntegers k))
    (hI : I ≠ 0) (v : NumberField.FinitePlace k)
    (hmap : IdealMapPowerStatement (k := k) I hI v)
    (hspan : LocalizedLineIdealMapStatement (k := k) I hI v)
    (huni : UniformizerPowerSpanStatement (k := k) v) :
    IdealLocalizedCountStatement (k := k) I hI v := by
  obtain ⟨pi, hpi⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
    (K := k) (v := underlyingPrime v)
  refine ⟨pi, _, rfl, ?_⟩
  rw [hspan, hmap]
  exact huni pi hpi _

def idealCountProofRows : List (String × String × String) :=
  [ ("IdealMapPowerStatement", "Ideal.map O_K->O_v I = completionIdeal^count", "GAP bridge 1"),
    ("LocalizedLineIdealMapStatement", "localizedLine = span of ideal-map image", "GAP bridge 2"),
    ("UniformizerPowerSpanStatement", "span of completionIdeal^e = span uniformizer^e", "GAP bridge 3 (FLT uniformizer)"),
    ("idealLocalizedCount_of_bridges", "3 bridges => IdealLocalizedCountStatement", "PROVED (conditional)") ]

theorem idealCountProofRows_length : idealCountProofRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual

end
