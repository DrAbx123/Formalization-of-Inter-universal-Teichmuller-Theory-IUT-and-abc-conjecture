/- G-C general-T psi: the first NON-EMPTY instance of the RR data (for T : Finset ℚ),
   cross-checking the interface against the existing B2 global zero-fibre theorem.

  `PsiGeneralRRDataWithDT` is the RR-data interface; here we instantiate it with the obvious
  rational-point data (u0 := psiChart0Coord = prod (X - t), u1 := psiChartInfCoord, compat =
  affine_compat_swapped) and the divisor DTFixed. The `hDT` field is exactly
  `psiChart0Coord_mem_iff` (a prime contains the product iff it contains one factor).
  As a consistency check we recover `psi^{-1}(0) = DTFixed` independently of B2Fixed5.
  The GENERAL Galois-stable T still needs Riemann-Roch (registered obligation). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGeneralZeroFibreDTActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed5Actual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralZeroFibreDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

variable (n : Nat) (T : Finset ℚ)

/-- **RR 数据的首个非空实例**（有理点集 T）：u0 = `psiChart0Coord`、u1 = `psiChartInfCoord`、
    `DT = DTFixed n T`。 -/
noncomputable def psiGeneralRRDataOfFinset : PsiGeneralRRDataWithDT n T where
  u0 := psiChart0Coord n T
  u1 := psiChartInfCoord n T
  haffine := affine_compat_swapped n T
  DT := DTFixed n T
  hDT := by
    show (fermatChart0ToCurve n) ''
        {p : PrimeSpectrum (R n) | psiChart0Coord n T ∈ p.asIdeal} = DTFixed n T
    unfold DTFixed
    congr 1
    ext p
    exact psiChart0Coord_mem_iff n T p.asIdeal

/-- **一致性检查**：由 RR-data 得到的 `ψ^{-1}(0) = DTFixed`（与 B2Fixed5 的全局定理一致）。 -/
theorem psiGeneralRRDataOfFinset_preimage_p1Zero_eq :
    (psiOfRRData n T (psiGeneralRRDataOfFinset n T).toPsiGeneralRRData) ⁻¹' p1Zero =
      DTFixed n T :=
  psiOfRRDataWithDT_preimage_p1Zero_eq n T (psiGeneralRRDataOfFinset n T)

#print axioms psiGeneralRRDataOfFinset
#print axioms psiGeneralRRDataOfFinset_preimage_p1Zero_eq
/-- **实例与 B2 的 `psiFixed` 一致**：RR-data 实例给出的 morphism 就是 `psiFixed n T`
    （两者 chart 函数与 overlap 兼容相同，差在证明项，proof irrelevance）。 -/
theorem psiGeneralRRDataOfFinset_eq_psiFixed :
    (psiOfRRData n T (psiGeneralRRDataOfFinset n T).toPsiGeneralRRData) = psiFixed n T := rfl

#print axioms psiGeneralRRDataOfFinset_eq_psiFixed
/-- **RR 数据存在性谓词**（供义务跟踪）：`PsiGeneralRRDataWithDT n T` 非空。
    对 `T : Finset ℚ`（有理点集）由下面的实例证明；**一般几何点集 T 的存在性由
    Riemann–Roch 给出，登记为显式义务**（见文件头/`coord/EXPLICIT-PARAM-AUDIT-GRACE.md` A3）。 -/
def HasPsiGeneralRRData (n : Nat) (T : Finset ℚ) : Prop :=
  Nonempty (PsiGeneralRRDataWithDT n T)

/-- 有理点集情形：存在性成立（由 `psiGeneralRRDataOfFinset`）。 -/
theorem hasPsiGeneralRRData_of_finset (n : Nat) (T : Finset ℚ) :
    HasPsiGeneralRRData n T := ⟨psiGeneralRRDataOfFinset n T⟩

#print axioms hasPsiGeneralRRData_of_finset



end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRInstanceActual