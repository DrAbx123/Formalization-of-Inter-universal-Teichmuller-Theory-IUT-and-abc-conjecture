/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Initial Theta: orbicurve signatures and Euler characteristic bookkeeping -/

namespace LeanFormal.IUT.XiFPaper.OrbicurveSignatureActual

/-- Orbicurve signature data: genus, punctures, stacky orders. -/
structure OrbicurveSignature where
  genus : Nat
  punctures : Nat
  stackyOrders : List Nat

/-- The (log) Euler characteristic of an orbicurve signature: 2 - 2g - n (orbifold part
recorded separately), as an integer. -/
def chi (S : OrbicurveSignature) : Int :=
  2 - 2 * (S.genus : Int) - (S.punctures : Int)

/-- The type (1,1) signature of the once-punctured torus. -/
def typeOneOne : OrbicurveSignature where
  genus := 1
  punctures := 1
  stackyOrders := []

theorem typeOneOne_genus : typeOneOne.genus = 1 := rfl

theorem typeOneOne_punctures : typeOneOne.punctures = 1 := rfl

theorem typeOneOne_chi : chi typeOneOne = -1 := by
  unfold chi typeOneOne
  norm_num

theorem chi_eq (S : OrbicurveSignature) :
    chi S = 2 - 2 * (S.genus : Int) - (S.punctures : Int) := rfl

end LeanFormal.IUT.XiFPaper.OrbicurveSignatureActual
