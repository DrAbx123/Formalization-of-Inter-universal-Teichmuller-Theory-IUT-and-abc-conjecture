# S2563: the discriminant of S2481HZ as an explicit 15x15 determinant

Date: 2026-11-05
Owner: worker (subagent of 26413cde-cfd3-431f-9d29-db37c555cb63)
Stage: proof (kernel closed), actual file
Consumer: the S2562/S2563 HZ_c monic chain (the value Dval is the
normalisation constant; S2563 identifies it with the discriminant of the
integer model S2481HZ).

## Target (locked)

    LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Dval
      = Polynomial.discr LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ

Both orientations are proved.

## File

tmp/sheaf/xif/paper/S2563DiscrMatrixActual.lean (278 lines), imports only
tmp.sheaf.xif.paper.S2562HZcMonicCActual.  No sorry, axiom, True/PUnit gate or
native_decide; no new assumptions.

## Proof (what is actually proved)

1. def M : Matrix (Fin 15) (Fin 15) Z is the explicit integer matrix of the
   task statement (rows 0..13 are the Sylvester rows of S2481HZ.derivative and
   S2481HZ, row 14 is the derivative-normalising row [0,..,1 at column 6,..,8 at
   column 14]).
2. M_eq_SD : M = Matrix.reindex castFin castFin S2481HZ.sylvesterDeriv.
   Note: sylvesterDeriv of f has type Matrix (Fin (f.natDegree - 1 +
   f.natDegree)); for S2481HZ this is Fin 15 only after rewriting natDegree = 8,
   so the comparison is made through castFin : Fin (natDegree - 1 + natDegree)
   ~= Fin 15, the identity on values.  castFin is a genuine equivalence
   (left_inv/right_inv by simp) and Matrix.det_reindex_self shows the
   determinant is unchanged, so nothing is weakened.  The entrywise proof is
   fin_cases on both indices (225 goals) with the coefficient lemmas
   S2481HZ_coeff_0 .. S2481HZ_coeff_8 (from S2481HZ = C a0 + monomial 2 a1 +
   monomial 4 a2 + monomial 6 a3 + monomial 8 a4) and Polynomial.coeff_derivative.
3. eblk : Fin 8 + Fin 7 ~= Fin 15 is the even/odd reindexing (inl r |-> 2r,
   inr s |-> 2s+1; inverse given explicitly by pattern matching).  M_block:
   reindex eblk.symm eblk.symm M = fromBlocks P 0 0 Q, entrywise over the two
   index sums (the 8x8 and 7x7 diagonal blocks are the even/odd blocks).  By
   Matrix.det_reindex_self and Matrix.det_fromBlocks_zero_21:
   det_M_blocks : M.det = P.det * Q.det.
4. P.det and Q.det.  PL/PU and QL/QU are explicit rational matrices with
   P.map (x |-> (x : Q)) = PL * PU and Q.map (x |-> (x : Q)) = QL * QU,
   verified entrywise (ext, fin_cases, norm_num); PL, QL are unit lower
   triangular and PU, QU upper triangular (PL_lower, PU_upper, QL_lower,
   QU_upper, entrywise with fin_cases and omega on the index inequality).
   Int.cast_det + det_mul + det_of_lowerTriangular + det_of_upperTriangular
   then give, over Q, ((P.det : Z) : Q) = (prod diag PL) * (prod diag PU) and
   similarly for Q; the two diagonal products are evaluated by
   Fin.prod_univ_succ + norm_num, and Int.cast_injective (exact_mod_cast)
   returns the integer statement:
     det_P : P.det = -7592406612899261915812258745010342024429497867849903723054940842779339653120000000000000000
     det_Q : Q.det = -572322530474177198990386439528222093828187251089135972479301025500259462397139353600000000
5. det_M : M.det = Dval  (rw [det_M_blocks, det_P, det_Q, Dval]; norm_num with
   the 79-digit literal).
6. discr_eq : Polynomial.discr S2481HZ = Dval.  Polynomial.discr unfolds to
   sylvesterDeriv.det * (-1)^(n*(n-1)/2); HZ_natDegree gives n = 8, so the sign
   is (-1)^28 = 1 and the statement reduces to M.det = Dval.
7. Dval_eq_discr : Dval = Polynomial.discr S2481HZ := discr_eq.symm.

## Verification actually run

* serial compile, exactly the prescribed policy command:
  cd D:/lean; lake env lean -j1 -R 'D:/lean' -o
  '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2563DiscrMatrixActual.olean'
  'tmp/sheaf/xif/paper/S2563DiscrMatrixActual.lean'
  EXIT = 0, 155.5 s, no errors and no warnings.
* SRC SHA256 E1F793CE468D15057AE9FE6226809394FCB17FE9B77D35C8673C4073538B5B54
  (15938 bytes).
* OLEAN SHA256 A4452AFF8EB5DA144FE3F3EF45FBDE1A70212C7EF49E3A3FEA94233F7E0EAFC9
  (9105048 bytes).
* #print axioms on M_eq_SD, M_block, det_M_blocks, P_LU, Q_LU, det_P, det_Q,
  det_M, discr_eq, Dval_eq_discr: every one depends on
  [propext, Classical.choice, Quot.sound] only.
* consumer check (tmp/sheaf/xif/paper/_S2563Consumer.lean, EXIT = 0) restates
  the locked target with fully qualified names
  (LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual.Dval =
   Polynomial.discr LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ)
  and its reverse, both by direct reference to the compiled module; axioms
  trio only.

## Statement / proof status

statement_compiles: yes (olean built)
proof_body_checked: yes (no sorryAx in any axiom print)
kernel_closed: yes, axioms trio only
target_accepted: comparator-level check done by the consumer restatement in the
same toolchain; not reviewed by an independent maintainer in this session.

## Boundary / notes

* The P/Q determinant values were computed independently in Python (sympy LU)
  and then certified inside Lean; the Lean proof does not trust the Python run.
* The prompt's transcription of the 8x8 and 7x7 blocks had the derivative-block
  columns shifted by one; the blocks actually used here are read off the
  Sylvester matrix definition (even rows x even columns = P, odd x odd = Q).
* Scratch files S2563Scratch1..9 and the generator scripts were removed; only
  the actual file and the consumer remain.
