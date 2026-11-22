import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AlgebraicClosure

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

#check algebraicClosure F W.FunctionField
#check (algebraicClosure F W.FunctionField).val
#check IntermediateField.val
#check (algebraicClosure F W.FunctionField).val.toAlgHom
#check Point.map (W' := W) (S := F) (F := (algebraicClosure F W.FunctionField)) (K := W.FunctionField) (algebraicClosure F W.FunctionField).val.toAlgHom

end
