import tmp.sheaf.xif.paper.S2562HZcMonicCActual

/-!
# S2563: the discriminant of S2481HZ via its explicit Sylvester determinant

The 15 x 15 matrix M below is the matrix S2481HZ.sylvesterDeriv.  After the
even/odd reindexing eblk it splits into two zero off-diagonal blocks, so its
determinant is P.det * Q.det; both factors are computed from verified LU
decompositions over the rationals.
-/

noncomputable section

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2563DiscrMatrixActual

open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

/-! ## 1. The explicit matrix -/

def M : Matrix (Fin 15) (Fin 15) ℤ := !![
    6153500390625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 6153500390625, 0, 0, 0, 0, 0, 16289971661250, 0, 0, 0, 0, 0, 0, 0;
    8144985830625, 0, 6153500390625, 0, 0, 0, 0, 0, 16289971661250, 0, 0, 0, 0, 0, 0;
    0, 8144985830625, 0, 6153500390625, 0, 0, 0, 23861749940224, 0, 16289971661250, 0, 0, 0, 0, 0;
    5965437485056, 0, 8144985830625, 0, 6153500390625, 0, 0, 0, 23861749940224, 0, 16289971661250, 0, 0, 0, 0;
    0, 5965437485056, 0, 8144985830625, 0, 6153500390625, 0, 26626851078144, 0, 23861749940224, 0, 16289971661250, 0, 0, 0;
    4437808513024, 0, 5965437485056, 0, 8144985830625, 0, 6153500390625, 0, 26626851078144, 0, 23861749940224, 0, 16289971661250, 0, 0;
    0, 4437808513024, 0, 5965437485056, 0, 8144985830625, 0, 3710851743744, 0, 26626851078144, 0, 23861749940224, 0, 16289971661250, 0;
    463856467968, 0, 4437808513024, 0, 5965437485056, 0, 8144985830625, 0, 3710851743744, 0, 26626851078144, 0, 23861749940224, 0, 16289971661250;
    0, 463856467968, 0, 4437808513024, 0, 5965437485056, 0, 0, 0, 3710851743744, 0, 26626851078144, 0, 23861749940224, 0;
    0, 0, 463856467968, 0, 4437808513024, 0, 5965437485056, 0, 0, 0, 3710851743744, 0, 26626851078144, 0, 23861749940224;
    0, 0, 0, 463856467968, 0, 4437808513024, 0, 0, 0, 0, 0, 3710851743744, 0, 26626851078144, 0;
    0, 0, 0, 0, 463856467968, 0, 4437808513024, 0, 0, 0, 0, 0, 3710851743744, 0, 26626851078144;
    0, 0, 0, 0, 0, 463856467968, 0, 0, 0, 0, 0, 0, 0, 3710851743744, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8]

/-! ## 2. Coefficients of S2481HZ -/

lemma HZ_deg : S2481HZ.natDegree - 1 + S2481HZ.natDegree = 15 := by rw [HZ_natDegree]

lemma S2481HZ_mono :
    S2481HZ = C 6153500390625 + monomial 2 8144985830625 + monomial 4 5965437485056 +
      monomial 6 4437808513024 + monomial 8 463856467968 := by
  unfold S2481HZ
  simp only [Polynomial.C_mul_X_pow_eq_monomial]

@[simp] lemma S2481HZ_coeff_0 : S2481HZ.coeff 0 = 6153500390625 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_1 : S2481HZ.coeff 1 = 0 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_2 : S2481HZ.coeff 2 = 8144985830625 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_3 : S2481HZ.coeff 3 = 0 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_4 : S2481HZ.coeff 4 = 5965437485056 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_5 : S2481HZ.coeff 5 = 0 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_6 : S2481HZ.coeff 6 = 4437808513024 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_7 : S2481HZ.coeff 7 = 0 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]
@[simp] lemma S2481HZ_coeff_8 : S2481HZ.coeff 8 = 463856467968 := by rw [S2481HZ_mono]; simp [Polynomial.coeff_monomial]

/-! ## 3. M is the Sylvester derivation matrix -/

/-- Identity on values between Fin (natDegree - 1 + natDegree) and Fin 15. -/
def castFin : Fin (S2481HZ.natDegree - 1 + S2481HZ.natDegree) ≃ Fin 15 where
  toFun i := ⟨i.val, by have h1 := i.isLt; have h2 := HZ_deg; omega⟩
  invFun j := ⟨j.val, by have h1 := j.isLt; have h2 := HZ_deg; omega⟩
  left_inv i := by simp
  right_inv j := by simp

/-- S2481HZ.sylvesterDeriv transported to Fin 15. -/
def SD : Matrix (Fin 15) (Fin 15) ℤ := Matrix.reindex castFin castFin S2481HZ.sylvesterDeriv

theorem M_eq_SD : M = SD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, SD, castFin, Matrix.reindex_apply, Matrix.submatrix_apply, Polynomial.sylvesterDeriv,
      HZ_natDegree, Polynomial.sylvester, Matrix.of_apply, Matrix.updateRow_apply,
      Polynomial.coeff_derivative, Fin.addCases]

/-! ## 4. The even/odd reindexing -/

def eodF : Fin 8 ⊕ Fin 7 → Fin 15
  | Sum.inl r => ⟨2 * r.val, by omega⟩
  | Sum.inr s => ⟨2 * s.val + 1, by omega⟩

def eodI (k : Fin 15) : Fin 8 ⊕ Fin 7 :=
  match k.val with
  | 0 => Sum.inl 0
  | 1 => Sum.inr 0
  | 2 => Sum.inl 1
  | 3 => Sum.inr 1
  | 4 => Sum.inl 2
  | 5 => Sum.inr 2
  | 6 => Sum.inl 3
  | 7 => Sum.inr 3
  | 8 => Sum.inl 4
  | 9 => Sum.inr 4
  | 10 => Sum.inl 5
  | 11 => Sum.inr 5
  | 12 => Sum.inl 6
  | 13 => Sum.inr 6
  | 14 => Sum.inl 7
  | _ => Sum.inl 0

def eblk : Fin 8 ⊕ Fin 7 ≃ Fin 15 where
  toFun := eodF
  invFun := eodI
  left_inv := by
    intro x
    rcases x with r | s
    · fin_cases r <;> rfl
    · fin_cases s <;> rfl
  right_inv := by
    intro k
    fin_cases k <;> rfl

/-! ## 5. The two blocks -/

def P : Matrix (Fin 8) (Fin 8) ℤ := !![
    6153500390625, 0, 0, 0, 0, 0, 0, 0;
    8144985830625, 6153500390625, 0, 0, 16289971661250, 0, 0, 0;
    5965437485056, 8144985830625, 6153500390625, 0, 23861749940224, 16289971661250, 0, 0;
    4437808513024, 5965437485056, 8144985830625, 6153500390625, 26626851078144, 23861749940224, 16289971661250, 0;
    463856467968, 4437808513024, 5965437485056, 8144985830625, 3710851743744, 26626851078144, 23861749940224, 16289971661250;
    0, 463856467968, 4437808513024, 5965437485056, 0, 3710851743744, 26626851078144, 23861749940224;
    0, 0, 463856467968, 4437808513024, 0, 0, 3710851743744, 26626851078144;
    0, 0, 0, 1, 0, 0, 0, 8]

def Q : Matrix (Fin 7) (Fin 7) ℤ := !![
    6153500390625, 0, 0, 16289971661250, 0, 0, 0;
    8144985830625, 6153500390625, 0, 23861749940224, 16289971661250, 0, 0;
    5965437485056, 8144985830625, 6153500390625, 26626851078144, 23861749940224, 16289971661250, 0;
    4437808513024, 5965437485056, 8144985830625, 3710851743744, 26626851078144, 23861749940224, 16289971661250;
    463856467968, 4437808513024, 5965437485056, 0, 3710851743744, 26626851078144, 23861749940224;
    0, 463856467968, 4437808513024, 0, 0, 3710851743744, 26626851078144;
    0, 0, 463856467968, 0, 0, 0, 3710851743744]

theorem M_block : Matrix.reindex eblk.symm eblk.symm M = Matrix.fromBlocks P 0 0 Q := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex, eblk, eodF, eodI, Matrix.fromBlocks, M, P, Q]

theorem det_M_blocks : M.det = P.det * Q.det := by
  rw [← Matrix.det_reindex_self eblk.symm M, M_block, Matrix.det_fromBlocks_zero₂₁]

/-! ## 6. LU factorisation of the two blocks over the rationals -/

noncomputable def PL : Matrix (Fin 8) (Fin 8) ℚ := !![
    (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((121743622144) / 125581640625), ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((4437808513024) / 6153500390625), ((121743622144) / 125581640625), ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((17179869184) / 227907421875), ((4437808513024) / 6153500390625), ((121743622144) / 125581640625), ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), ((17179869184) / 227907421875), ((4437808513024) / 6153500390625), ((121743622144) / 125581640625), ((33183608501898273973726363648) / 65415294833617202201681900625), (1 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), ((17179869184) / 227907421875), ((4437808513024) / 6153500390625), ((902143627151472134674456772608) / 3205349446847242907882413130625), ((7995843793294492896673757425557323776) / 22383614466859615013137023563678867269), (1 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), ((1) / 6153500390625), ((197201177102598817) / 3205349446847242907882413130625), ((343777093185829373712888319) / 5730205303516061443363078032301790020864), ((335500146590491677164169491071) / 1208846010273382736009816039722860166512640), (1 : ℚ)]

noncomputable def PU : Matrix (Fin 8) (Fin 8) ℚ := !![
    (6153500390625 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), (6153500390625 : ℚ), (0 : ℚ), (0 : ℚ), (16289971661250 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), (6153500390625 : ℚ), (0 : ℚ), (2299780339262 : ℚ), (16289971661250 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (6153500390625 : ℚ), ((394402354205197634) / 50625), (2299780339262 : ℚ), (16289971661250 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((-52740978449880334352578) / 2562890625), ((394402354205197634) / 50625), (2299780339262 : ℚ), (16289971661250 : ℚ);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((-15695819118601554661971285971066466672110993408) / 1103883100317290287153382073046875), ((4302327981536040229570878202558533337088) / 445002005670865321099876875), ((58761882617247275574236926036377600) / 3767212746420023882327);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((-271695045737353451480394242996931719400986960199680) / 22383614466859615013137023563678867269), ((7523666118159800204395879351995576845705557311488) / 456808458507339081900755582932221781);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((1718822713206426952511414485397338502) / 1152845392487890945443931617472515265)]

lemma PL_lower : PL.BlockTriangular OrderDual.toDual := by
  intro i j h
  have h' : i.val < j.val := h
  fin_cases i <;> fin_cases j <;> simp [PL] at h' ⊢

lemma PU_upper : PU.BlockTriangular id := by
  intro i j h
  have h' : j.val < i.val := h
  fin_cases i <;> fin_cases j <;> simp [PU] at h' ⊢

lemma P_LU : P.map (fun x => (x : ℚ)) = PL * PU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, PL, PU, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem det_P : P.det = -7592406612899261915812258745010342024429497867849903723054940842779339653120000000000000000 := by
  have h : ((P.det : ℤ) : ℚ) = ((-7592406612899261915812258745010342024429497867849903723054940842779339653120000000000000000 : ℤ) : ℚ) := by
    rw [Int.cast_det, P_LU, Matrix.det_mul, Matrix.det_of_lowerTriangular PL PL_lower,
      Matrix.det_of_upperTriangular (M := PU) PU_upper]
    have hPL : (∏ i : Fin 8, PL i i) = 1 := by
      simp [Fin.prod_univ_succ, PL]
    have hPU : (∏ i : Fin 8, PU i i) =
        ((-7592406612899261915812258745010342024429497867849903723054940842779339653120000000000000000 : ℤ) : ℚ) := by
      simp [Fin.prod_univ_succ, PU]
      norm_num
    rw [hPL, hPU, one_mul]
  exact_mod_cast h

noncomputable def QL : Matrix (Fin 7) (Fin 7) ℚ := !![
    (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((121743622144) / 125581640625), ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((4437808513024) / 6153500390625), ((121743622144) / 125581640625), ((67009) / 50625), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    ((17179869184) / 227907421875), ((4437808513024) / 6153500390625), ((121743622144) / 125581640625), ((33183608501898273973726363648) / 65415294833617202201681900625), (1 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), ((17179869184) / 227907421875), ((4437808513024) / 6153500390625), ((902143627151472134674456772608) / 3205349446847242907882413130625), ((7995843793294492896673757425557323776) / 22383614466859615013137023563678867269), (1 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), ((17179869184) / 227907421875), ((3387890425553463822493155328) / 118716646179527515106756041875), ((622903235208925054527991725667909632) / 22383614466859615013137023563678867269), ((148414528846942622243759329426096128) / 1152845392487890945443931617472515265), (1 : ℚ)]

noncomputable def QU : Matrix (Fin 7) (Fin 7) ℚ := !![
    (6153500390625 : ℚ), (0 : ℚ), (0 : ℚ), (16289971661250 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), (6153500390625 : ℚ), (0 : ℚ), (2299780339262 : ℚ), (16289971661250 : ℚ), (0 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), (6153500390625 : ℚ), ((394402354205197634) / 50625), (2299780339262 : ℚ), (16289971661250 : ℚ), (0 : ℚ);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), ((-52740978449880334352578) / 2562890625), ((394402354205197634) / 50625), (2299780339262 : ℚ), (16289971661250 : ℚ);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((-15695819118601554661971285971066466672110993408) / 1103883100317290287153382073046875), ((4302327981536040229570878202558533337088) / 445002005670865321099876875), ((58761882617247275574236926036377600) / 3767212746420023882327);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((-271695045737353451480394242996931719400986960199680) / 22383614466859615013137023563678867269), ((7523666118159800204395879351995576845705557311488) / 456808458507339081900755582932221781);
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), ((797287032811107834269342790400081750605416103936) / 1152845392487890945443931617472515265)]

lemma QL_lower : QL.BlockTriangular OrderDual.toDual := by
  intro i j h
  have h' : i.val < j.val := h
  fin_cases i <;> fin_cases j <;> simp [QL] at h' ⊢

lemma QU_upper : QU.BlockTriangular id := by
  intro i j h
  have h' : j.val < i.val := h
  fin_cases i <;> fin_cases j <;> simp [QU] at h' ⊢

lemma Q_LU : Q.map (fun x => (x : ℚ)) = QL * QU := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, QL, QU, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem det_Q : Q.det = -572322530474177198990386439528222093828187251089135972479301025500259462397139353600000000 := by
  have h : ((Q.det : ℤ) : ℚ) = ((-572322530474177198990386439528222093828187251089135972479301025500259462397139353600000000 : ℤ) : ℚ) := by
    rw [Int.cast_det, Q_LU, Matrix.det_mul, Matrix.det_of_lowerTriangular QL QL_lower,
      Matrix.det_of_upperTriangular (M := QU) QU_upper]
    have hQL : (∏ i : Fin 7, QL i i) = 1 := by
      simp [Fin.prod_univ_succ, QL]
    have hQU : (∏ i : Fin 7, QU i i) =
        ((-572322530474177198990386439528222093828187251089135972479301025500259462397139353600000000 : ℤ) : ℚ) := by
      simp [Fin.prod_univ_succ, QU]
      norm_num
    rw [hQL, hQU, one_mul]
  exact_mod_cast h

/-! ## 7. The determinant and the discriminant -/

theorem det_M : M.det = Dval := by
  rw [det_M_blocks, det_P, det_Q, Dval]
  norm_num

theorem discr_eq : Polynomial.discr S2481HZ = Dval := by
  have h1 : S2481HZ.sylvesterDeriv.det = M.det := by
    rw [← Matrix.det_reindex_self castFin S2481HZ.sylvesterDeriv]
    show SD.det = M.det
    rw [← M_eq_SD]
  rw [Polynomial.discr, h1, HZ_natDegree]
  norm_num
  exact det_M

/-- Main result: Dval is the discriminant of the integer model. -/
theorem Dval_eq_discr : Dval = Polynomial.discr S2481HZ := discr_eq.symm

#print axioms M_eq_SD
#print axioms M_block
#print axioms det_M_blocks
#print axioms P_LU
#print axioms Q_LU
#print axioms det_P
#print axioms det_Q
#print axioms det_M
#print axioms discr_eq
#print axioms Dval_eq_discr

end LeanFormal.IUT.XiFPaper.S2563DiscrMatrixActual

end
