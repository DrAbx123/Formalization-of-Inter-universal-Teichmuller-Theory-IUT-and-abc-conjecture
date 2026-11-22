import LeanFormal.IUT.Foundations.LocalFields.ContinuousRationalPadicScalars
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Continuous ring maps respect Qp when its algebra maps are continuous

The two ring maps from Q agree by the proved uniqueness of rational ring
homomorphisms. Their extensions agree on Qp by rational density and
continuity. Only the native semiring data of RingHom and Algebra are needed.
-/

namespace LeanFormal.IUT.LocalFieldPadicScalars

noncomputable section

variable {p : ℕ} [Fact p.Prime] {E F : Type*}
variable [Semiring E] [Semiring F] [TopologicalSpace E] [TopologicalSpace F] [T2Space F]
variable [Algebra ℚ_[p] E] [Algebra ℚ_[p] F]

def continuousRingHomAlgHom (f : E →+* F) (hf : Continuous f)
    (hE : Continuous (algebraMap ℚ_[p] E)) (hF : Continuous (algebraMap ℚ_[p] F)) :
    E →ₐ[ℚ_[p]] F where
  toRingHom := f
  commutes' a := by
    change f (algebraMap ℚ_[p] E a) = algebraMap ℚ_[p] F a
    have hrat : f.comp ((algebraMap ℚ_[p] E).comp (algebraMap ℚ ℚ_[p])) =
        (algebraMap ℚ_[p] F).comp (algebraMap ℚ ℚ_[p]) := Subsingleton.elim _ _
    have heq := (Padic.denseRange_ratCast p).equalizer (hf.comp hE) hF (by
      funext q
      exact DFunLike.congr_fun hrat q)
    exact congrFun heq a

theorem continuousRingHomAlgHom_apply (f : E →+* F) (hf : Continuous f)
    (hE : Continuous (algebraMap ℚ_[p] E)) (hF : Continuous (algebraMap ℚ_[p] F)) (x : E) :
    continuousRingHomAlgHom (p := p) f hf hE hF x = f x := rfl

theorem continuous_continuousRingHomAlgHom (f : E →+* F) (hf : Continuous f)
    (hE : Continuous (algebraMap ℚ_[p] E)) (hF : Continuous (algebraMap ℚ_[p] F)) :
    Continuous (continuousRingHomAlgHom (p := p) f hf hE hF) := hf

theorem continuousRingHom_commutes (f : E →+* F) (hf : Continuous f)
    (hE : Continuous (algebraMap ℚ_[p] E)) (hF : Continuous (algebraMap ℚ_[p] F)) (a : ℚ_[p]) :
    f (algebraMap ℚ_[p] E a) = algebraMap ℚ_[p] F a :=
  (continuousRingHomAlgHom (p := p) f hf hE hF).commutes a

end

end LeanFormal.IUT.LocalFieldPadicScalars
