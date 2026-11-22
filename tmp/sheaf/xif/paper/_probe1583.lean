import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
open Matrix
namespace Probe
variable {l : PrimeGeFive}
def J : Matrix (Fin 2) (Fin 2) (ZMod l.value) := !![0, -1; 1, 0]
def U : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two]; norm_num⟩
#check @J
#check @U
example : (U (l := l) : Matrix (Fin 2) (Fin 2) (ZMod l.value)) = !![1,1;0,1] := rfl
end Probe
