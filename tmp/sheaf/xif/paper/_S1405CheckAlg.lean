import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open WeierstrassCurve
open scoped WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

example : (W.baseChange F).IsElliptic := by
  change (W.map (algebraMap F F)).IsElliptic
  infer_instance

example (Ω : Type*) [Field Ω] [Algebra F Ω] : (W.baseChange Ω).IsElliptic := by
  change (W.map (algebraMap F Ω)).IsElliptic
  infer_instance
