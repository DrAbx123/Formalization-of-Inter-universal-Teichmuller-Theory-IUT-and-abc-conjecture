/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Reference: Gogopex/iut-lean (Iut/Foundations/Species.lean + Iut/Stage1/PilotComparison.lean).
Copied with attribution; combined and adapted only for local build. -/
import Mathlib.Data.Real.Basic
/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
/-!
Foundational bookkeeping for the IUT formalization.

This file starts with a deliberately small interface for species, mutations, and
labeled copies. It is not yet a formalization of Mochizuki's set-theoretic
species/mutation formalism; it is a typed scaffold for the first Stage 1 models.
-/

namespace Iut

universe u v

/-- A provisional species is a type of objects. Morphisms and formulas will be
added only when a concrete formalization step needs them. -/
structure Species where
  Obj : Type u

/-- A provisional mutation maps objects of one species to objects of another. -/
structure Mutation (source : Species.{u}) (target : Species.{v}) where
  mapObj : source.Obj -> target.Obj

/-- A copy of an object with an explicit label. The label is part of the data. -/
structure LabeledCopy (alpha : Type u) where
  label : String
  carrier : alpha
deriving Repr

namespace LabeledCopy

variable {alpha : Type u}

/-- Forget the label attached to a copy. This operation is intentionally explicit. -/
def forget (x : LabeledCopy alpha) : alpha :=
  x.carrier

@[simp]
theorem forget_mk (label : String) (carrier : alpha) :
    forget ({ label := label, carrier := carrier } : LabeledCopy alpha) = carrier :=
  rfl

/-- Two labeled copies are label-compatible when their labels agree. -/
def LabelCompatible (x y : LabeledCopy alpha) : Prop :=
  x.label = y.label

/-- Two labeled copies have the same underlying carrier after labels are forgotten. -/
def SameCarrier (x y : LabeledCopy alpha) : Prop :=
  x.forget = y.forget

end LabeledCopy

/-- A named indeterminacy, together with the bookkeeping needed in early models. -/
structure Indeterminacy where
  name : String
  actsOnLogShells : Bool
  absorbedByHull : Bool
deriving Repr

/-- A finite list of indeterminacies carried by a construction. -/
abbrev IndeterminacyProfile :=
  List Indeterminacy

end Iut

/-!
Stage 1 interface: the target shape of the implication from IUT III,
Theorem 3.11 to Corollary 3.12.

The structures below do not assert IUT. They isolate the real-valued comparison
that a later formalization must justify from explicit multiradial, hull, and
indeterminacy hypotheses.
-/

namespace Iut.Stage1

/-- Names for the two pilot sides whose comparison is central in Corollary 3.12. -/
inductive PilotSide where
  | q
  | theta
deriving DecidableEq, Repr

/-- A real log-volume value tagged by its pilot side. -/
structure PilotLogVolume where
  side : PilotSide
  value : Real

/-- The bare real inequality appearing in the statement of Corollary 3.12. -/
def Corollary312Inequality (theta q : PilotLogVolume) : Prop :=
  -theta.value >= -q.value

/--
Minimal endpoint package for a Stage 1 comparison.

The field `comparison` is the Corollary-3.12-shaped conclusion itself. Thus
`corollary312_from_stage1_comparison` is only a projection from this endpoint
package, not a source proof of the comparison. Source-facing routes must derive
such a package from descent, hull+det, simultaneous holomorphic expressibility,
input prime-strip links, and allowed indeterminacies.
-/
structure Stage1Comparison where
  theta : PilotLogVolume
  q : PilotLogVolume
  theta_side : theta.side = PilotSide.theta
  q_side : q.side = PilotSide.q
  q_positive : 0 < q.value
  comparison : Corollary312Inequality theta q

/-- Projection of the conclusion stored in a completed endpoint package. -/
theorem corollary312_from_stage1_comparison (data : Stage1Comparison) :
    Corollary312Inequality data.theta data.q :=
  data.comparison

end Iut.Stage1

