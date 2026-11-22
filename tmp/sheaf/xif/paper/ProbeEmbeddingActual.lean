import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.GroupWithZero.WithZero

noncomputable section
open MonoidWithZeroHom

namespace LeanFormal.IUT.XiFPaper.ProbeEmbeddingActual

variable {A B : Type*} [MonoidWithZero A] [MonoidWithZero B] [GroupWithZero B] (f : A →*₀ B)

theorem embedding_unitsWithZeroEquiv_symm (g : valueGroup f) :
    ValueGroup₀.embedding (f := f) ((WithZero.unitsWithZeroEquiv (α := valueGroup f)).symm g).1 =
      (g.1 : B) := by
  let u : (ValueGroup₀ f)ˣ := (WithZero.unitsWithZeroEquiv (α := valueGroup f)).symm g
  change ValueGroup₀.embedding (f := f) u.1 = (g.1 : B)
  rfl

end LeanFormal.IUT.XiFPaper.ProbeEmbeddingActual
end
