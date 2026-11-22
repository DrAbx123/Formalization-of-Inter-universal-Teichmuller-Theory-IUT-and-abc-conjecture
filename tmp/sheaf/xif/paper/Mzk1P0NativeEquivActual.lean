/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0NativeSourceCoreActual
import Mathlib.Tactic
/-! # P0: old-core fields to native core projections; impossible fields as explicit GAP -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeEquivActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
universe u
def oldC3ImpossibleFields : List String :=
  ["roots : NatRootSystem (candidateUnits place q)", "qUnit : unit of completion at FinitePlaceAtPrime", "tensorLanding_q : tensorLanding q = tensorUnit"]
theorem oldC3ImpossibleFields_length : oldC3ImpossibleFields.length = 3 := rfl
def migratableFields : List String :=
  ["p/place/q", "qUnit (as Units.mk0 q)", "tensorIndex/tensorPlaces/tuple", "tensorBlock", "qCoeff"]
theorem migratableFields_length : migratableFields.length = 5 := rfl
def rows : List String := ["migratable: p/place/q, qUnit, tensor fields", "impossible: completion roots, completion qUnit, tensorLanding_q", "native core provides qCoeff/tensorBlock/roots", "no old C3 / no IsEmpty"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeEquivActual
end