/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve

/-! # A743: real constructor for `InitialThetaArithmeticData` from supplied field/curve data -/

/- `InitialThetaArithmeticData l` (ArithmeticData.lean:62-81) fields:
* data: Fmod, F, K (each a Type with Field/NumberField instances),
  tower : ThetaFieldTower l Fmod F K, curve : PuncturedEllipticCurve F;
* instance fields: algebra/tower/Galois/finite-dim instances (filled by inferInstance here).
This file constructs the record from explicit parameters: NO field is assumed via axiom; the
tower data (sqrt(-1), degree-prime-to-l, other ThetaFieldTower fields) and the curve are real
parameters, since a general construction from lana `InitialThetaData` still needs the
A.Fmod/A.K/tower transfers (A742 gaps). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ArithmeticDataConstructionActual

open LeanFormal.IUT

universe u

variable {l : PrimeGeFive}
variable (Fmod F K : Type u)
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]

/-- The real constructor: every structure field is either a supplied datum or an instance. -/
noncomputable def mkInitialThetaArithmetic
    (tower : ThetaFieldTower l Fmod F K)
    (curve : PuncturedEllipticCurve F) :
    InitialThetaArithmeticData.{u} l where
  Fmod := Fmod
  fieldFmod := inferInstance
  numberFieldFmod := inferInstance
  F := F
  fieldF := inferInstance
  numberFieldF := inferInstance
  K := K
  fieldK := inferInstance
  numberFieldK := inferInstance
  algebraFmodF := inferInstance
  algebraFK := inferInstance
  algebraFmodK := inferInstance
  towerFmodFK := inferInstance
  finiteFmodF := inferInstance
  galoisFmodF := inferInstance
  finiteFK := inferInstance
  galoisFK := inferInstance
  tower := tower
  curve := curve

/-- Projection: the constructed record's base field is the supplied `F`. -/
theorem mkInitialThetaArithmetic_F (tower : ThetaFieldTower l Fmod F K)
    (curve : PuncturedEllipticCurve F) :
    (mkInitialThetaArithmetic (l := l) Fmod F K tower curve).F = F := rfl

/-- Projection: the reconstructed moduli field is the supplied `Fmod`. -/
theorem mkInitialThetaArithmetic_Fmod (tower : ThetaFieldTower l Fmod F K)
    (curve : PuncturedEllipticCurve F) :
    (mkInitialThetaArithmetic (l := l) Fmod F K tower curve).Fmod = Fmod := rfl

/-- Projection: the constructed record carries exactly the supplied curve. -/
theorem mkInitialThetaArithmetic_curve (tower : ThetaFieldTower l Fmod F K)
    (curve : PuncturedEllipticCurve F) :
    (mkInitialThetaArithmetic (l := l) Fmod F K tower curve).curve = curve := rfl

/-- Projection: the constructed record carries exactly the supplied tower. -/
theorem mkInitialThetaArithmetic_tower (tower : ThetaFieldTower l Fmod F K)
    (curve : PuncturedEllipticCurve F) :
    (mkInitialThetaArithmetic (l := l) Fmod F K tower curve).tower = tower := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ArithmeticDataConstructionActual
