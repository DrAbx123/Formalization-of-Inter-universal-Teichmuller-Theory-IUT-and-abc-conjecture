import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalContraction
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTensorPower

/-!
# The local tensor point map of III Example 3.6

Layer 3: the canonical map from the local contracted product T_v = Gamma_v x^G T
to the local contracted product of the n-fold contracted product T^oT n:

  phi_n : T_v ---> (T^oT n)_v,   [a, t] |---> [n a, t^oT n].

This makes the n-th power of a local point an actual point of the
tensor-power object (not only a coordinate).  It is well defined because the
tensor base point changes by the n-th power: tensorPoint (h t) = h^n tensorPoint t,
and delta(h^n) = n delta(h).

Consequences: the coordinate law
  localCoord (tensorPoint t) (phi_n p) = n * localCoord t p,
and the description of the tensor power of the local point [a,t] as [n a, t^oT n].
These are the local input for reading degree-n torsor arrows as actual
equivariant maps of tensor powers.

Boundary: local contraction only (any additive value group Gamma); no global
torsor category or source identification.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open GTorsorTensor

universe u v

variable {F : Type u} [Field F] {Gamma : Type v} [AddCommGroup Gamma]

/-- The tensor base point changes by the n-th power: the n-fold tensor of the
translated point `h • t` is obtained from the n-fold tensor of `t` by the
action of `h^n` (the i0-coordinate action of the contracted product). -/
theorem GTorsorTensor.tensorPoint_smul_pow {T : GTorsor Fˣ} (n : ℕ) (i0 : Fin n)
    (h : Fˣ) (t : T.carrier) :
    tensorPoint T n (h • t) = tensorSMul T n i0 (h ^ n) (tensorPoint T n t) := by
  letI : MulAction Fˣ (tensorCarrier T n) := tensorMulAction T n i0
  change tensorPoint T n (h • t) = h ^ n • tensorPoint T n t
  have hcoord : (tensorPowerAt T n i0).coordinate (tensorPoint T n t)
      (tensorPoint T n (h • t)) = h ^ n := by
    rw [tensorPowerAt_coordinate_tensorPoint]
    rw [GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]
  have hspec := (GTorsor.coordinate_eq_iff (tensorPowerAt T n i0)
    (tensorPoint T n t) (tensorPoint T n (h • t)) (h ^ n)).mp hcoord
  exact hspec.symm

namespace LocalTensorPoint

variable (D : LocalValueData F Gamma) (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)

/-- The n-fold tensor point map `phi_n : T_v -> (T^⊗n)_v`, defined on the
representative `(a,t)` by `[n a, t^⊗n]`. -/
def localTensorPointMap : LocalContraction D T →
    LocalContraction D (tensorPowerAt T n i0) :=
  Quotient.lift
    (fun q : Gamma × T.carrier =>
      localContractionMk D (tensorPowerAt T n i0)
        (n • q.1, tensorPoint T n q.2))
    (by
      intro q q' hrel
      obtain ⟨g, rfl⟩ := hrel
      have hpt : tensorPoint T n (g • q.2) =
          tensorSMul T n i0 (g ^ n) (tensorPoint T n q.2) :=
        GTorsorTensor.tensorPoint_smul_pow n i0 g q.2
      rw [hpt]
      letI : MulAction Fˣ (tensorCarrier T n) := tensorMulAction T n i0
      refine (localContractionMk_eq_iff (D := D) (T := tensorPowerAt T n i0)).mpr ?_
      refine ⟨g ^ n, ?_⟩
      ext
      · rw [LocalValueData.deltaAdd_pow, smul_sub]
      · rfl)

@[simp]
theorem localTensorPointMap_mk (a : Gamma) (t : T.carrier) :
    localTensorPointMap D T n i0 (localContractionMk D T (a, t)) =
      localContractionMk D (tensorPowerAt T n i0) (n • a, tensorPoint T n t) :=
  rfl

/-- The tensor point map sends the local point of coordinate `a` to the local
point of coordinate `n • a` relative to the tensor base point. -/
theorem localTensorPointMap_localPoint (t : T.carrier) (a : Gamma) :
    localTensorPointMap D T n i0 (localPoint D T t a) =
      localPoint D (tensorPowerAt T n i0) (tensorPoint T n t) (n • a) :=
  rfl

/-- **Coordinate law**: the coordinate of the tensor point of `p` relative to
the tensor base point is `n` times the coordinate of `p`. -/
theorem localCoord_localTensorPointMap (t : T.carrier)
    (p : LocalContraction D T) :
    localCoord D (tensorPowerAt T n i0) (tensorPoint T n t)
      (localTensorPointMap D T n i0 p) = n • localCoord D T t p := by
  induction p using Quotient.inductionOn with
  | h q =>
      rw [localTensorPointMap_mk, localCoord_mk, localCoord_mk]
      rw [tensorPowerAt_coordinate_tensorPoint, LocalValueData.deltaAdd_pow]
      rw [smul_add]

end LocalTensorPoint

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
