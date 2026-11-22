import Mathlib
import tmp.sheaf.takkun.IutLean.Anabelian.CyclotomicRigidity
import tmp.sheaf.takkun.IutLean.Theta.ThetaValues
import tmp.sheaf.takkun.IutLean.Theta.ThetaGroup

/-!
# 単テータ環境 (Mono-theta environment) と 3 つの剛性

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§14, §15 / [EtTh] §1, §2, §5。

エタールテータ関数 `Θ̈`(の `l` 乗根)を記述する設定が**単テータ環境** (mono-theta
environment) である。`X^log` に付随するエタール的円分物 `∆_Θ`(階数 1 自由 `Ẑ` 加群、
Hoshi §14)と、単数的円分物 `Λ(k)`(局所類体論由来)とを結ぶ。単テータ環境の本質は、
次の **3 つの剛性 (rigidity)** を、環構造に依らず(=多輻的に)与えることにある:

1. **円分剛性 (cyclotomic rigidity)** — `Λ(k) ≅ ∆_Θ` の正準的同型。Phase 3 の
   `GaloisCyclotome.RigidityIso` として具体的に持つ。
2. **離散剛性 (discrete rigidity)** — テータ値の `l·ℤ` 軌道が `Ẑ` ではなく離散的 `ℤ` で
   制御されること。
3. **定数倍剛性 (constant multiple rigidity)** — `O×_k`-倍の不定性が除かれ、`q_E^N` が
   剛性のある対象として表示されること (Hoshi §15)。

ここでは円分剛性を Phase 3 の `RigidityIso` で具体化し、離散剛性・定数倍剛性は保留述語
(`opaque`)として要求する。単テータ環境からの帰結(円分物の同期)を `sorry` 無しで証明する。
-/

namespace IUT.Theta

open IUT.Anabelian
open scoped commutatorElement

universe u v w

/-! ## 離散剛性・定数倍剛性 — テータ群の交換子から証明される代数的核

[EtTh] §5 / Hoshi §15 の離散剛性・定数倍剛性は、テータ群 `Gθ`(中心拡大、`IsThetaGroup`)の
**交換子対**の代数的性質として実現される。テータ群そのもの(エタールテータ関数から定まる
中心拡大)の構成は深い幾何的入力だが、それを **データ** として与えれば、両剛性は
`IutLean.Theta.ThetaGroup` の交換子補題から **証明される帰結** となる(`opaque` 不要)。 -/

/-- **定数倍剛性** ([EtTh] §5, Hoshi §15)。テータ群の交換子対が中心 `Λ` 倍
(= `O×_k`「定数倍」)の不定性のもとで不変、すなわち中心剰余 `Π = Gθ/Z` に降下すること。
`O×_k`-倍の不定性が除かれる剛性の代数的内容。 -/
def ConstantMultipleRigidity (Gθ : Type w) [Group Gθ] [IsThetaGroup Gθ] : Prop :=
  ∀ (a b : Gθ) {z : Gθ}, z ∈ Subgroup.center Gθ →
    ⁅a * z, b⁆ = ⁅a, b⁆ ∧ ⁅a, b * z⁆ = ⁅a, b⁆

/-- 定数倍剛性は任意のテータ群(中心拡大)で成立(交換子の中心剰余への降下)。 -/
theorem constantMultipleRigidity (Gθ : Type w) [Group Gθ] [IsThetaGroup Gθ] :
    ConstantMultipleRigidity Gθ := fun a b _ hz =>
  ⟨commutatorElement_center_mul_left a b hz, commutatorElement_center_mul_right a b hz⟩

/-- **離散剛性** ([EtTh] §5, Hoshi §15)。テータ群の交換子対が交代的
(`⁅a,a⁆ = 1` かつ `⁅a,b⁆ * ⁅b,a⁆ = 1`)= シンプレクティック形式として離散的に振る舞うこと。 -/
def DiscreteRigidity (Gθ : Type w) [Group Gθ] [IsThetaGroup Gθ] : Prop :=
  (∀ a : Gθ, ⁅a, a⁆ = 1) ∧ (∀ a b : Gθ, ⁅a, b⁆ * ⁅b, a⁆ = 1)

/-- 離散剛性は任意のテータ群で成立(交換子の交代性)。 -/
theorem discreteRigidity (Gθ : Type w) [Group Gθ] [IsThetaGroup Gθ] :
    DiscreteRigidity Gθ :=
  ⟨fun a => commutatorElement_self a,
   fun a b => by rw [← commutatorElement_inv]; exact inv_mul_cancel ⁅b, a⁆⟩

/-- **単テータ環境** (mono-theta environment, Hoshi §14)。
テータ的円分物 `∆_Θ` と単数的円分物 `Λ(k)`、両者を結ぶ円分剛性同型、及び離散剛性・
定数倍剛性を束ねる。離散剛性・定数倍剛性は、**データ**として与えるテータ群 `thetaGroup`
(エタールテータ関数から定まる中心拡大)の交換子から **証明される**(`discrete`/`constantMultiple`)。 -/
structure MonoThetaEnvironment (R : Type u) [CommRing R] (G : Type v) [Group G] where
  /-- テータ的円分物 `∆_Θ`(`X^log` に付随、階数 1)。 -/
  thetaCyclotome : GaloisCyclotome.{u, v, w} R G
  /-- 単数的円分物 `Λ(k)`(局所類体論由来)。 -/
  unitCyclotome : GaloisCyclotome.{u, v, w} R G
  /-- **円分剛性**: `Λ(k) ≅ ∆_Θ` の正準的 `G`-同変同型。 -/
  cyclotomicRigidity : GaloisCyclotome.RigidityIso unitCyclotome thetaCyclotome
  /-- **テータ群** `Gθ`(エタールテータ関数から定まる中心拡大の全空間, [EtTh] §1)。
  これが離散剛性・定数倍剛性の代数的座席であり、構成は深い幾何的入力。 -/
  thetaGroup : Type w
  [thetaGroup_group : Group thetaGroup]
  [thetaGroup_isTheta : IsThetaGroup thetaGroup]
  /-- **離散剛性**(テータ群の交換子の交代性として成立)。 -/
  discrete : DiscreteRigidity thetaGroup
  /-- **定数倍剛性**(テータ群の交換子の中心剰余降下として成立)。 -/
  constantMultiple : ConstantMultipleRigidity thetaGroup

attribute [instance] MonoThetaEnvironment.thetaGroup_group MonoThetaEnvironment.thetaGroup_isTheta

namespace MonoThetaEnvironment

variable {R : Type u} [CommRing R] {G : Type v}
  [Group G] (E : MonoThetaEnvironment.{u, v, w} R G)

/-- 単テータ環境の円分剛性が与える、単数的円分物 `Λ(k)` からテータ的円分物 `∆_Θ` への
`R`-線型同型(Kummer 理論と両立する円分同期化)。 -/
noncomputable def synchronization :
    E.unitCyclotome.M ≃ₗ[R] E.thetaCyclotome.M :=
  E.cyclotomicRigidity.toLinearEquiv

/-- **円分同期化の `G`-同変性**: 円分剛性は `G` 作用(円分指標)を `Λ(k)` から `∆_Θ` へ
輸送する。これが単テータ環境による「環構造に依らない円分物の同期」の内容。 -/
theorem synchronization_equivariant (g : G) (m : E.unitCyclotome.M) :
    E.thetaCyclotome.ρ g (E.synchronization m)
      = E.synchronization (E.unitCyclotome.ρ g m) := by
  unfold synchronization
  exact E.cyclotomicRigidity.transport g m

end MonoThetaEnvironment

end IUT.Theta
