/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.KummerRootRatio

/-! # A511 glue: Kummer root-ratio bundle consumers -/

noncomputable section

namespace LeanFormal.IUT.Objects.KummerRatio

open LeanFormal.IUT

variable {G M U : Type*} [Group G] [CommGroup M] [CommGroup U] {value : M}

/-- The Kummer root-ratio data together with injectivity of the ratio map: the bundle on
which the zero/addition ratio laws are usable. -/
structure KummerRatioBundle where
  /-- The ratio data. -/
  data : KummerRootRatioData G M U value
  /-- The ratio map is injective. -/
  injective : Function.Injective data.ratioMap

/-- The ratio at exponent zero is trivial (consumer of `ratioUnit_zero`). -/
theorem KummerRatioBundle.ratioUnit_zero (B : KummerRatioBundle (value := value))
    (g : B.data.subgroup) : B.data.ratioUnit g 0 = 1 :=
  KummerRootRatioData.ratioUnit_zero B.data B.injective g

/-- The ratio is additive in its rational exponent (consumer of `ratioUnit_add`). -/
theorem KummerRatioBundle.ratioUnit_add (B : KummerRatioBundle (value := value))
    (g : B.data.subgroup) (q₁ q₂ : ℚ) :
    B.data.ratioUnit g (q₁ + q₂) = B.data.ratioUnit g q₁ * B.data.ratioUnit g q₂ :=
  KummerRootRatioData.ratioUnit_add B.data B.injective g q₁ q₂

/-- The ratio map sends the ratio unit to the Galois action difference (source field). -/
theorem KummerRatioBundle.ratioMap_ratioUnit (B : KummerRatioBundle (value := value))
    (g : B.data.subgroup) (q : ℚ) :
    B.data.ratioMap (B.data.ratioUnit g q) =
      B.data.action (g : G) (B.data.rootSystem.roots q).toMul /
        (B.data.rootSystem.roots q).toMul :=
  B.data.ratio_spec g q

end LeanFormal.IUT.Objects.KummerRatio
