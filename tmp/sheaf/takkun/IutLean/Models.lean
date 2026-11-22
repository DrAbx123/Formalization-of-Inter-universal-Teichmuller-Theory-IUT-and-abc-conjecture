import Mathlib
import tmp.sheaf.takkun.IutLean.Anabelian.CyclotomicRigidity
import tmp.sheaf.takkun.IutLean.Frobenioid.Basic
import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs
import tmp.sheaf.takkun.IutLean.LogTheta.Indeterminacy
import tmp.sheaf.takkun.IutLean.Multiradial.MainTheorem
import tmp.sheaf.takkun.IutLean.Theta.MonoTheta

/-!
# 具体モデル: 抽象構造の非空性と具体的成立例

本ファイルでは、これまで定義した抽象構造(`GaloisCyclotome`, `RigidityIso`,
`LogShellIndeterminacy`, `Frobenioid.Model`)の**具体的なインスタンス**を構成し、
それらが**空でない(非空)**ことを `sorry` 無しに証明する。

特に:
* **円分同期化同型**(`CyclotomicSynchronizationExists` の意図)が、具体的な円分物のモデルで
  実際に成立すること(`trivialCyclotome_rigidity`)、
* **多輻的表示の well-definedness** が具体的な不定性のモデルで成立すること
  (`regularIndeterminacy_wellDefined`)、
* **フロベニオイド**の枠組みが非空であること(`frobenioid_nonempty`)

を、具体構成によって示す。これにより、抽象的な定義が*空虚でない*ことが保証される。
-/

namespace IUT.Models

open IUT.Anabelian IUT.Frobenioid

/-! ## 円分物と円分同期化の具体モデル -/

/-- **自明な Galois 円分物**: 基底 `ℤ`(`≅ Ẑ` の最も簡単なモデル)に群 `G` が自明に作用するもの。 -/
def trivialCyclotome (G : Type) [Group G] : GaloisCyclotome ℤ G where
  M := ℤ
  isCyclotome := ⟨LinearEquiv.refl ℤ ℤ⟩
  ρ := 1

/-- **円分同期化同型の具体的成立例**: 自明円分物の間には円分剛性同型が存在する。
深い `CyclotomicSynchronizationExists`(一般の曲線では基本類 `H²(Q,Ẑ)≅Ẑ` を要する)が、
この具体モデルでは実際に `sorry` 無しで成立することを示す。 -/
theorem trivialCyclotome_rigidity (G : Type) [Group G] :
    Nonempty (GaloisCyclotome.RigidityIso (trivialCyclotome G) (trivialCyclotome G)) :=
  ⟨GaloisCyclotome.RigidityIso.refl _⟩

/-- 円分剛性同型の構造輸送が、この具体モデルでも成立(`G` 作用=自明指標の同期)。 -/
theorem trivialCyclotome_transport (G : Type) [Group G]
    (f : GaloisCyclotome.RigidityIso (trivialCyclotome G) (trivialCyclotome G))
    (g : G) (m : ℤ) :
    (trivialCyclotome G).ρ g (f.toLinearEquiv m)
      = f.toLinearEquiv ((trivialCyclotome G).ρ g m) :=
  f.transport g m

/-! ## 単テータ環境の具体モデル -/

/-- **単テータ環境の具体的成立例**: 自明円分物 `ℤ` と自明(可換)テータ群 `Multiplicative ℤ`
から単テータ環境が構成でき、**離散剛性・定数倍剛性**(深い `[EtTh]` の剛性、従来は `opaque`)が
テータ群の交換子から `sorry` 無しで成立することを示す。可換テータ群では交換子はすべて自明で、
交代性(離散剛性)・中心剰余降下(定数倍剛性)が即座に従う。 -/
noncomputable def trivialMonoThetaEnvironment (G : Type) [Group G] :
    Theta.MonoThetaEnvironment.{0, 0, 0} ℤ G where
  thetaCyclotome := trivialCyclotome G
  unitCyclotome := trivialCyclotome G
  cyclotomicRigidity := GaloisCyclotome.RigidityIso.refl _
  thetaGroup := Multiplicative ℤ
  discrete := Theta.discreteRigidity _
  constantMultiple := Theta.constantMultipleRigidity _

/-- 単テータ環境の枠組みは非空(離散剛性・定数倍剛性を含めて充足可能)。 -/
theorem monoThetaEnvironment_nonempty (G : Type) [Group G] :
    Nonempty (Theta.MonoThetaEnvironment.{0, 0, 0} ℤ G) :=
  ⟨trivialMonoThetaEnvironment G⟩

/-! ## 不定性と多輻的表示の具体モデル -/

/-- **左正則作用による不定性のモデル**: 群 `G` が自身に左並進で作用するものを、対数殻の
不定性 `LogShellIndeterminacy` の具体例とする。(Ind3) 上半両立性は `upperSemiCompatibility`
で具体的に証明される。 -/
def regularIndeterminacy (G : Type) [Group G] : LogTheta.LogShellIndeterminacy where
  Γ := G
  I := G
  ind3 := LogTheta.upperSemiCompatibility G G

/-- **多輻的表示の well-definedness の具体的成立例**: 上記モデルにおいて、object (a) の
多輻的出力が不定性のもとで不変であることが `sorry` 無しで成立する。 -/
theorem regularIndeterminacy_wellDefined (G : Type) [Group G] :
    Multiradial.MultiradialWellDefined (regularIndeterminacy G) :=
  Multiradial.multiradialWellDefined _

/-! ## 素点縞系と Hodge 劇場の具体モデル -/

/-- 自明な D-プライム縞(全素点で自明群、射影は恒等)。 -/
def trivialDPrimeStrip (V : Type) : Frobenioid.DPrimeStrip.{0} V where
  Pi _ := PUnit
  G _ := PUnit
  proj _ := MonoidHom.id PUnit
  proj_surjective _ := Function.surjective_id

/-- **素点縞系の具体的成立例**(旧 `opaque HasPrimeStripSystem` の脱ブラックボックス化の
非空性証明): 単一素点 `Unit`、自明な Galois 群、単項式 `Multiplicative ℤ`、q-parameter
`= ofAdd 1`(無限位数!)からなる素点縞系。**非退化性**(`j ≠ 0` でテータ値 `q^{j²} ≠ 1`)を
`sorry` 無しで証明 ―― q-parameter が無限位数であることが本質(`V^bad ≠ ∅` の反映)。 -/
def trivialPrimeStripSystem (l : ℕ) [Fact l.Prime] : HodgeTheater.PrimeStripSystem l where
  V := Unit
  addSystem := Frobenioid.constantLabeledSystem Unit (LabCuspPM l) (GeoSym l)
    (trivialDPrimeStrip Unit)
  mulSystem := Frobenioid.constantLabeledSystem Unit (LabCusp l) (LabCusp l)
    (trivialDPrimeStrip Unit)
  gaussian :=
    { G := fun _ => PUnit
      Mon := fun _ => Multiplicative ℤ
      action := fun _ => 1
      qParam := fun _ => Multiplicative.ofAdd 1 }
  glue _ := ⟨fun _ => MulEquiv.refl PUnit⟩
  nondegenerate := ⟨(), by
    intro j hj h1
    have h2 : 0 < j ^ 2 := lt_of_le_of_ne (sq_nonneg j) (Ne.symm (pow_ne_zero 2 hj))
    have hN : (IUT.Theta.gaussExp j).toNat ≠ 0 := by
      unfold IUT.Theta.gaussExp; omega
    apply hN
    simp only [Frobenioid.GaussianPrimeStrip.thetaValueAt, Frobenioid.FhPrimeStrip.gaussianValue,
      IUT.Theta.thetaValueMon] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_pow, toAdd_ofAdd, toAdd_one, nsmul_eq_mul, mul_one] at h3
    exact_mod_cast h3⟩

/-- 旧 opaque `HasPrimeStripSystem` の後継命題は**成立する**(witness による非空性)。 -/
theorem hasPrimeStripSystem (l : ℕ) [Fact l.Prime] : HodgeTheater.HasPrimeStripSystem l :=
  ⟨trivialPrimeStripSystem l⟩

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Θ±ellNF Hodge 劇場の最初のインスタンス**: `l = 5`(最小の許容素数)と具体的素点縞系から、
加法的(D-Θ±ell)・乗法的(D-ΘNF)Hodge 劇場を構成し、共通素数で貼り合わせる。
旧 opaque の下では構成不可能だった Full Hodge 劇場が**実際に構成できる**ことの実証。 -/
def modelHodgeTheater : HodgeTheater.Full where
  add := { l := 5, l_ge_five := le_refl 5, primeStrips := trivialPrimeStripSystem 5 }
  mul := { l := 5, l_ge_five := le_refl 5, primeStrips := trivialPrimeStripSystem 5 }
  glue := rfl

/-- Θ±ellNF Hodge 劇場の枠組みは**非空**。 -/
theorem hodgeTheater_nonempty : Nonempty HodgeTheater.Full :=
  ⟨modelHodgeTheater⟩

/-! ## フロベニオイドの具体モデル -/

/-- **自明なフロベニオイド**: `O▷ = ℕ`(乗法モノイド)、数論的次数を自明(≡ 0)としたもの。 -/
def trivialFrobenioid : Frobenioid.Model where
  base := { Otri := ℕ }
  deg := 1

/-- フロベニオイドの枠組みは非空。 -/
theorem frobenioid_nonempty : Nonempty Frobenioid.Model :=
  ⟨trivialFrobenioid⟩

end IUT.Models
