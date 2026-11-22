import tmp.sheaf.xif.paper.PaperC3KummerExtensionActual
import Mathlib.RingTheory.AdjoinRoot

-- Global finite Kummer number-field model: actual AdjoinRoot carrier and the
-- exact missing global q lift / NumberField instance.
--
-- G.qUnit is a completion unit. To form Kprime = Fmod[X]/(X^(2l)-q_global)
-- with an actual NumberField instance and a completion root, one needs a
-- global q lift q_global ∈ K with q_global ↦ G.qUnit in the completion.
-- No such lift is present in the completion-valued geometry.  This file
-- constructs the actual AdjoinRoot carrier conditional on the lift and records
-- the exact NumberField/global-lift gap, without faking either.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperKummerNumberFieldModelActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3KummerExtensionActual
open Polynomial

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v : V)

-- Exact global q lift needed for a global Kummer extension.
structure GlobalQLift where
  completionMap : K →+* CommonPrimeCompletion (G.place v)
  globalQ : K
  globalQ_map :
    completionMap globalQ =
      (G.qUnit v : CommonPrimeCompletion (G.place v))

-- The actual Kummer polynomial over K, conditional on a global q lift.
noncomputable def kummerPolynomial (L : GlobalQLift (G := G) v) : Polynomial K :=
  X ^ (2 * l.value) - C L.globalQ

-- The actual AdjoinRoot carrier K[X]/(X^(2l)-q_global).
abbrev KummerAdjoinRoot (L : GlobalQLift (G := G) v) : Type u :=
  AdjoinRoot (kummerPolynomial (G := G) (l := l) v L)

-- The actual root class in the AdjoinRoot carrier.
noncomputable def kummerAdjoinRootRoot
    (L : GlobalQLift (G := G) v) : KummerAdjoinRoot (G := G) (l := l) v L :=
  AdjoinRoot.root (kummerPolynomial (G := G) (l := l) v L)

-- Exact NumberField/global-lift model.  Does not assert an inhabitant.
structure ActualKummerNumberFieldModel where
  lift : GlobalQLift (G := G) v
  Kprime : Type u
  field : Field Kprime
  numberField : NumberField Kprime
  algebra : K →+* Kprime
  completionEmbedding : Kprime →+* CommonPrimeCompletion (G.place v)
  rootImage : Kprime
  rootImage_pow : rootImage ^ (2 * l.value) = algebra lift.globalQ
  rootImage_map_pow :
    completionEmbedding rootImage ^ (2 * l.value) =
      (G.qUnit v : CommonPrimeCompletion (G.place v))

def ActualKummerNumberFieldModelRequired : Prop :=
  Nonempty (ActualKummerNumberFieldModel (G := G) (v := v))

#check GlobalQLift
#check kummerPolynomial
#check KummerAdjoinRoot
#check kummerAdjoinRootRoot
#check ActualKummerNumberFieldModel
#check ActualKummerNumberFieldModelRequired

end LeanFormal.IUT.XiFPaper.PaperKummerNumberFieldModelActual

end