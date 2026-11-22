# C9 consolidated error and survivor ledger

Task: task-164 (C9 consolidated error/survivor ledger)
Owner: multiradial
Date: 2026-10-25
Stage: SHEAF stage1 verification/consolidation, natural language only.
No Lean/Project edits. Only this file written. No new attack claim.

Status: consolidated. The C9 corpus contains a valid arithmetic core, a
conditional source layer, a conditional/withdrawn target layer, and several
confirmed errors. This ledger records the confirmed errors, the survivors, the
current file hashes, and the stale-version warnings. It does not close P6 and
does not assert any target inequality.

## 0. Scope and authority

Authoritative corrections:

- C9-SYMPLECTIC-SOURCE-20261025.md (task-147) corrects the TAME Section 2
  symplectic donor.
- C9-IND1-GLOBAL-20261025.md (task-149) corrects the TAME Section 5
  target-container step and records TC-A to TC-H.
- C9-ERRATA-SYMPLECTIC-20261025.md and C9-ERRATA-IND1-20261025.md are binding
  short-form errata.
- C9-MODP-GENERATOR-20261025.md (task-153) records the full finite-image
  branch as UNDETERMINED.
- C9-MODP-CERTIFICATE-20261025.md (task-155) records the trace computation and
  the conditional subgroup statement; the current file is conditional, but the
  original headline B=O_K is a full-barGamma overclaim.
- C9-MODP-BRANCH-PROOF-20261025.md and C9-AUDIT-BRANCH-20261025.md reconcile
  task-153 and task-155.
- C9-AUDIT-ARITH-20261025.md independently rechecks the arithmetic and arch
  labels.
- C9-AUDIT-TARGET-CONTAINER-20261025.md (task-159) audits task-148/151
  dependence on the withdrawn target step.

No Lean, Project, kernel, comparator, or independent review is part of this
ledger. The ledger is natural-language verification of the research files.

## 1. Current file hashes and stale-version warnings

Authoritative hashes of the current bytes:

File | Lines | SHA256
-----|------:|-------
C9-TAME-LOG-DOMAIN-20261025.md | 251 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06
C9-SYMPLECTIC-SOURCE-20261025.md | 314 | 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70
C9-IND1-GLOBAL-20261025.md | 532 | 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8
C9-ERRATA-SYMPLECTIC-20261025.md | 14 | A189FC87D9F633916A097C2B8D9C5BDA7407825920765C1CECA36335BE5024C7
C9-ERRATA-IND1-20261025.md | 14 | EF63F916B4312A3E8562D16C2C122770BF7F188B75760989F958FDA2F6A0F8C2
C9-MODP-GENERATOR-20261025.md | 345 | 8232226E983D95C4495864B7491A864750BF730B03611BC27FC5B5E25D39507C
C9-MODP-CERTIFICATE-20261025.md | 250 | E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95
C9-MODP-BRANCH-PROOF-20261025.md | 257 | AF543BBBC50E8EC8CF9909CD5675D830018254760ABC66410C81501A7227EADE
C9-AUDIT-BRANCH-20261025.md | 240 | C914E001B45EFE3755D09463DA4D85C78214B56975FAE7042E52BB8A5A56777D
C9-AUDIT-ARITH-20261025.md | 184 | 84B3151F87D5414CFA481893577E0497A776B8FA6D50AC12B87C8B24E47AE61E
C9-UNIFORM-HULL-20261025.md | 255 | 99539B279B008CBEE367C14BC48AC11114460B0C0B706A71546FFDDC245A7D5B
C9-GLOBAL-ASSEMBLY-20261025.md | 253 | 6AB115790D8CDFD9E261985F7F209E4817C572AF6AAF4A48EB0EFDC2DE52CCF2
C9-ARCH-GLOBAL-20261025.md | 198 | 524E078AD85C72067627F006D165A724436E1BA508E86475C5F991860586E489
C9-AUDIT-TARGET-CONTAINER-20261025.md | 581 | B6F748C63EE441509440704CEEF69764C542355A3AF5FE18ABD39159E44F3F47
C9-RADIUS-CORRECTION-20261025.md | 119 | D563226D8FCDE7E01F06BCDDD5195F19530182F828C3B419997F78AB3188405D
C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md | 230 | 8E7EF66A737BBFE73ED13EA568875A4D1305F48D814DE4B3773BEBB3DB2F3548
C9-LOG-DOMAIN-EXTEND-20261025.md | 200 | CC52A8CF0D5FB56172A7AF2F6FB0C5C57EB726A5A459D3CCDE42FDDD3DAF2DFA
C9-ARCHIMEDEAN-20261025.md | 251 | F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957
C9-AUDIT-LOG-ARCH-20261025.md | 299 | F7AD81083A1772BF5A300B1B05886C28831B8BBE11BAB1B097C5A817C12547EC
C9-AUDIT-ARCH-GLOBAL-20261025.md | 294 | 7D719850564C1550D9D525EBE01AE395FE2AE5D70214F21AA83293EC73154825
C9-LOG-DOMAIN-CORRECTION-20261025.md | 307 | 882DFDEF2BF11377EBC6FDC488205623804100CC54DEEACD5EC805E75F481655
C9-AUDIT-GLOBAL-ASSEMBLY-20261025.md | 280 | 916DC332D9AA15D5898062EC73C3D37E56A6CA682A9411DA0470C68647E22E6B
C9-GAMMA-COLUMN-ATTACK-20261025.md | 140 | 7BB5D789C5DFDA4CDDB9F39267D2AFCB961BBD369A2FD5983DAD2DC67378568C
C9-CANONICAL-NORM-ATTACK-20261025.md | 314 | B13902F60B129135B33324E763880DA5C90B175A83E0E639293D3844DD48408B
C9-FULL-OUT-COLUMN-ATTACK-20261025.md | 135 | 7CC2DDD03CFEFA97E38049CA1CCB90016E944DECE0185F706E42F7F97CD61FD8
C9-OTHER-LOCAL-TYPES-ATTACK-20261025.md | 169 | 489708DD6D1DE159036BFADD6D6484D4470A09E31B6CD97B8F81094F3B1184DB
C9-AUDIT-AGGREGATE-BI-20261025.md | 188 | 1FB1B8AB077BEB88058E9C8AF608B1D2E2C5C8E26FABBFA7F0FCE9FFCA0FD42B
C9-NORMALIZATION-DECISION-20261025.md | 267 | 5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D
C9-AUDIT-B-TYPEGAP-20261025.md | 127 | 540825E769E9F2895CE2FA327719C9A5A1F46BFA751E8865CB2A16E4322BAB27
C9-AUDIT-NORMALIZATION-DECISION-20261025.md | 348 | 79384B32506BA7F1849BB140DC1C2CDF298748F569898417C0E8FEC3B7E10A6C
C9-CONSTRUCT-E-20261025.md | 122 | 0F4E95CD0F21921BAF93F3CC8A29BDD4BC582055B13C827D576572B74C8D422D
C9-CONSTRUCT-KCK-20261025.md | 173 | E250D5C545AC6F152275B0FC9EC0E4966FF2917318D01B4C684143645C7FD40A
C9-HAFULL-ALPHA1-20261025.md | 145 | BA8459C4500B8E73ACFA12A3C20431C5FDF8ED1AF077DDD453F5D3C4F2E6A43B
C9-AUDIT-HAFULL-LITE-20261025.md | 378 | EF755618B74DC45913A6DD148E1E60ABC97CB6C4188748AC6F907EF9305FF223
C9-AUDIT-HAFULL-ALPHA1-20261025.md | 199 | 8B63FF614DE6E3E041C850C5AB829D60EE376A7EF622176A9760F97D0A9D80A6
C9-HAFULL-CORRECTED-ATTACK-20261025.md | 271 | A1BDFD61B7FB90D1D24EC9A3D770C308360A095F435D4A2C9F35509775356BF0
C9-AUDIT-MOD41-IMAGE-20261025.md | 290 | 834873837713EEE9AFA9E056E6B5682FA6D00DFE391322B8DC3B97677F8998D3
C9-MOD41-IMAGE-20261025.md | 201 | 993DE815B8442E2F44CC39877E597F7BD474180234EABE5EF4AE27DF25BBF21F
C9-MOD41-IMAGE-CORR2-20261025.md | 215 | 78FD8184AD13DC1C1DFCB2BDB90A7B92A5ECE737A6B92F83945844AEBF727140
C9-DPRIMES-KODAIRA-20261025.md | 142 | DA7DFD3137E0D0287403390DAEE4039F5681648748E0366FF8D7A0A8A382AC70
C9-ALTERNATIVE-E-PROFILE-20261025.md | 148 | 6E231A5D7EB23B8ACBB78E8FAEB21C6C3C8733829955628719CE1CBB8CD5A5AC
C9-AUDIT-UNIT-FILTRATION-20261025.md | 318 | 8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09
C9-ALT-E-COMPLETION-20261025.md | 139 | C991A8C3C8752E0908F46843583A8509F0259A33C6E1FC8C195CB93E18EEDD85
C9-PRINCIPAL-FILTRATION-P-20261025.md | 236 | F125420F44405B360A289CDF1787C6C4F979D122EB6E65072639DF1B6E160599
C9-AUDIT-MOD41-ALT-E-20261025.md | 246 | D8B982FD1F99C5F0147ABD3BE3333A8254E7F1F1977063DA9A0F6511F320E9CA
C9-MOD41-ALT-E-20261025.md | 166 | EB8CD3705E46AA800F99E14C974FF0EF70FB3E38F62D3CE44C22A8F044C70971
C9-Y1-TRACE-20261025.md | 179 | A33EBDB8D0D0551B1391CF3069C71B8CF3255D8B56F20F96513C7F33E22F425C
C9-MOD41-ALT-E-CORR2-20261025.md | 143 | D790C770F187897B45594B31FC0BF83BA09BE7BA1FCF69A380389535460AB0E9
C9-F-XI-CONSTRUCT-20261025.md | 192 | A301BBEB1204E84ECAA2D0C6A6A94967D88A789088E56EA4471B7A4F3F09B924
C9-NL-UNDERDETERMINATION-20261025.md | 301 | AAFE2BC84D93DEBACF06298B38D7B20694B6A04A0ADBF262DDB87D366E4D0582
C9-AUDIT-NL-UNDERDETERMINATION-20261025.md | 222 | BF9C2D8FF14315162DFC9FF96E520EDB7F9245797F7F891E4ECF0FEAEDBB5D99
C9HAFullConditional.lean | 175 | 042581D674A9742BDC8CF0560B7037E864ABC1AE50E89CF15E532908C8167FAE
C9HAFullConditional.olean | - | DE05EEAABCB0596D9982164EB9E0954C1799CA9EEB1C9222052EC1431183E1C2
C9UOrthogonal.lean | 148 | 656D46D2D5E6D468AFC27D72B78A64F63580D578F4610DC85D389596E260C41D
C9UOrthogonal.olean | - | 21A710373ACC53E995AB6521F52DBE832793413C1AA11BDF207496DD7D924CA8
C9-NONNORMALIZED-CONSTRUCTION-20261025.md | 314 | 6E16AA274D78A1FBAE7F7453BAF497DA03653B2F2A098225EF70C428AB6E2348
C9-MOD41-EXACT-G-20261025.md | 213 | 443A59656B1C1A7DDF3E921307FDFAE54BEAF50CDAF4542624AB3FD3A1B18ECC
C9-EXPLICIT-C-EQUATIONS-CORR2-20261025.md | 121 | C7884D5BC5B000989044C16AD174214C5837EC6DB387FAB9EC73DFEF309E5CF1
C9-FSEM-DEGREE-EXACT-20261025.md | 171 | FFEDC1EE1912C97538AB13CB0409FC6DB4C186621BB015B084516B1DB1F46CC1
C9-PSI41-COMPUTE-20261025.md | 151 | 92672F3AD168FC8BA7A258DB5624129FB693A0073338841B6910EE5877871A88
psi41_mod_primes.json | 24228 | 074096F0202476DA3B3CA9A3257E4A4E827E64AFAACAA9DDA58DA6F3BD0332FD
velu_quotient_mod_primes.json | 1142 | 716CAEC83C759D467BCA50FEB39083DFA378F157F2396B2563E79DC27D01F8DE
C9-MOD41-UNCONDITIONAL-20261025.md | 203 | 4EAF8135EFF70D6D5D79B6EB66A250F58B04A1E3FF4DA6210624684A4D6F9C25
C9-P6-SIGN-AUDIT-20261025.md | 241 | F4797C04CC87F6397CB15A5A4355B22DBEA179FC5895CD06AF1DE774918409A9
C9-LOGIC-CORRECTION-20261025.md | 180 | A0DC631787154E821DB664344BAB425D8EDEFF848DC19EB336F7E2DF6B0C21C9
C9-P6-NOGO-20261025.md | 181 | 7B9BB3256363B6A8D0931E4E55C62D6FFA27E1FD2A0BF421DC35744D9167557D

Stale-version warnings:

W1. Task-155 report hash dad8163ff6ccbbe81faea5b8b341f8a9b2d3c664931dd9fe5b7a49fd73b29be8
does not match the current C9-MODP-CERTIFICATE-20261025.md SHA256
E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95.
The current file is 250 lines, not the reported 236/9487 bytes. Use the current
hash. The errata file C9-ERRATA-IND1-20261025.md still cites the stale dad8163
hash; its content is correct but its version pointer is stale.

W2. Task-148 report says 232 lines; current C9-UNIFORM-HULL-20261025.md has 255
lines and SHA256 99539B279B008CBEE367C14BC48AC11114460B0C0B706A71546FFDDC245A7D5B.
Use the current hash. C9-ARCH-GLOBAL-20261025.md cites an older
C9-UNIFORM-HULL hash 2bf7a8c4...; that is stale.

W3. C9-AUDIT-BRANCH-20261025.md input table lists task-153 as 345 lines,
task-155 as 249 lines, task-147 as 313 lines, task-149 as 531 lines; current
files are 345, 250, 314, 532 respectively. The hashes for task-153/147/149
match current; task-155 hash matches current in the branch audit, but the line
counts and the task-155 report hash are stale. Use hashes as identity.

W4. Task-147 report file hash 3f98f68a... matches current C9-SYMPLECTIC-SOURCE.
Task-149 report hash 94785726... matches current C9-IND1-GLOBAL.
Task-151 report hash 6ab11579... matches current C9-GLOBAL-ASSEMBLY.

W5. All line counts in this ledger are informative; SHA256 is authoritative.
Trailing-newline counting can differ by one.

W6. The archimedean radius values in task-156 C9-ARCH-GLOBAL A18/A19 and
task-162 C9-GLOBAL-ASSEMBLY-CORRECTED D1/D2 are stale and invalid. They used
base e=41 or omitted log p. Use E8 and C9-RADIUS-CORRECTION-20261025.md; the
correct base is p=12301, and all prior radius figures are withdrawn.

W7. The C9-AUDIT-ARCH-GLOBAL input table lists task-156 as 197 lines, task-150
as 250 lines, and task-149 as 580 lines; current files are 198, 251, and 581
lines. The hashes match current. C9-AUDIT-LOG-ARCH's audited task-146/task-150
hashes match current. Use hashes, not stale line counts.

W8. Task-170's final report says 306 lines but current
C9-LOG-DOMAIN-CORRECTION-20261025.md has 307 lines; its input table lists
task-146 as 199 lines while current C9-LOG-DOMAIN-EXTEND is 200. Hashes match.
Use the current hash.

W9. Task-173's audit table cites C9-ERROR-LEDGER-20261025.md at 495 lines and
SHA256 06F8E743... That was the ledger before E9-E14 were appended. The current
ledger has a new hash. E8/E9-E14 content is additive; E13's conclusions on
task-156/162 are unaffected, but the ledger hash pointer in task-173 is stale.
Also task-173 lists task-156 as 197 lines while current C9-ARCH-GLOBAL is 198.

W10. Task-165 cites C9-AUDIT-BRANCH-20261025.md as 239 lines; current is 240
lines. The hash C914E001... matches current. C9-GAMMA-COLUMN-ATTACK current is
140 lines, SHA256 7BB5D789C5DFDA4CDDB9F39267D2AFCB961BBD369A2FD5983DAD2DC67378568C.
Use hashes, not stale line counts.

W11. C9-CANONICAL-NORM-ATTACK-20261025.md changed after the first task-174
revision: old SHA 2AD0DE86... is stale; current SHA is
B13902F60B129135B33324E763880DA5C90B175A83E0E639293D3844DD48408B (314 lines).
Use the current hash in E15.

W12. E18 supersedes any strict reading of the aggregate N=34 result. N=34 is
an equality (34S=D3), not strict closure; strict closure needs N>=35 or actual
h_inf>0. The B=I aggregate attack is conditional and no actual C realizes the
configuration. Fixed-p repeated counts are impossible; arbitrary-prime N=1 is
abstract.

W13. E16 is type-gapped: the Kondo y-basis lies in J and maps to 0 in I/J. All
literal I/J first-column/B-branch statements in task-153/154/155/165 are
conditional on the missing H_A-full integral lift; do not cite them as actual
I/J theorems. Task-155 trace table/subgroup statement survives conditionally.

W14. E19 binding normalization is B_I-zero. The shell-pi forms h_inf=log(r/pi),
h_inf<=0, and r>=pi*p^{d_p} are withdrawn as binding. task-156/162/166/176
shell-pi radii are stale; binding values are r>=p^{d_p}, b=3
5.0106595585e40 (log10 40.6998948963), b=273 log10 3878.759836402.

W15. E20 supersedes the literal B-branch reading of TAME Section 6 and
invalidates full-Gamma B=O_K/B=I/Q1 as written. task-153/154/155/165/180 are
type-gapped/conditional: only the p=12301 trace table, y_i->0 in I/J, x1-fixing
in k_+, Q_p-linearity, and Aut(K)-fixes-l survive without H_A/H_A-full.

W16. E21 label corrections: 40.6998948963 and 3878.759836402 are log10 RADIUS
(and log10 p^{d_p}), not log10 D. Actual log10 D_3=1.9718089764...,
log10 D_273=3.9509085787.... A_arc=11.5logpi is the final
procession-normalized weighted-average bound, not the raw maximal container
((j+1)logpi). D_C/d_p/radii remain conditional on finite donor/TC. E19/E13
wording is corrected accordingly.

W17. E22 invalidates the task-183 q=p^6 candidate: q=p^6 is algebraic with
0<|q|_p<1, so Mahler-Manin makes J(p^6) transcendental; j(E)=J(q_Tate) is
algebraic, so no E/F has Tate parameter p^6 at p=12301. task-183's rational
j(p^6) candidate is unusable. This is conditional on the cited Mahler-Manin
theorem; no alternative local q/actual E is constructed.

W18. E23 replaces the task-183 exact q=p^6 candidate by an actual E_j with
j0=1/p^6, so q=p^6+744p^12+... != p^6, but v_p(q)=6 and qhat=q^{1/82}=pi^3 v
(order 3) is actual at p. E22's exact q=p^6 no-go is not contradicted; E23 is a
partial actual skeleton, not a complete C. Stable reduction/semistabilization,
other bad q-orders, mod-41 SL2, explicit C_K/V/epsilon remain missing.

W19. RESOLVED by task-203: task-196 is correct, task-200 is erroneous, and
E24/task-195 is INVALID. W=ker Tr is a Q_p-hyperplane, NOT contained in the
Z_p-lattice J; the W subset J step is false. E26 gives the corrected canonical
alpha_+(1) formula and exact H_A-full criterion. H_A-full for full Out remains
OPEN; B=O_K conditional on H_A-full; B=I not available under H_A-full and not
constructed outside; b=3 B=I 9/41 not selected; b=3 B=O_K 408/41 conditional,
not actual.

W20. Conflict resolved: task-196 audit C9-AUDIT-HAFULL-LITE
SHA EF755618... is correct; task-200 audit C9-AUDIT-HAFULL-ALPHA1
SHA 8B63FF61... is erroneous and must not be cited as a pass. E24 is invalid;
E26 is the corrected route. The definitional point is settled: W is the Q_p
trace kernel, not the Z_p-span pi..pi40.

W21. task-205 mod-41 GL2/order 2,755,200/determinant-full claim is INVALID.
E27 audit (83487383...) corrects the point counts/signs/determinant orders;
E31 correction2 (78FD8184...) supersedes task-205 and repairs the transfer.
Valid: SL2(F41) subset G subset GL2(F41), 68,880<=|G|<=2,755,200,
projective orders 7/5, determinant order-10 subgroup, conditional 2,3-smooth
transfer. Exact |G|/|H|/determinant missing.

W22. task-198's claim that E_j is good at 2,3 is INVALID. E28 (DA7DFD31...)
shows both are bad additive; D-primes are Kodaira III*, local semistabilization
degree 4, D-part degree 2-power <=512, F_sem total degree 2,3-smooth and 41
not dividing. Exact 2,3 types/global F_sem degree missing. E29 (6E231A5D...)
adds actual alternative E with b=1; strict Q(zeta12) fails because E[2]=S3.

W23. task-204's premise that every Out(G_K) preserves the upper ramification
filtration is INVALID. E30 (8D715581...) cites Kondo 2025 Theorem A: only the
finite Aut(k) preserves it. H=Phi^{-1}(Sp) is infinite, so choose alpha in
H\Aut(k); alpha^times(U^n)!=U^n. Valid: U^e=1+pO_K, exp/log, Kondo log
compatibility, a(alpha)=alpha_+(1). Invalid: a(alpha) in O_K for all Out,
H_A-full, B=O_K/B=I for full Out. Only Aut(k)/Gamma0 subgroup is conditional;
full B branch OPEN.

W24. task-212 alternative E completion C9-ALT-E-COMPLETION
SHA C991A8C3... (139 lines; supersedes stale ad3614b2 pointer) is an actual
source-level candidate with p local type I_1, v_p(q)=1, formal b=1/2, and
qhat=pi^{1/2} not in K_v. It does NOT satisfy C9 e=41/f=1/b=3/q=p^6u^6;
use only as an alternative I_1 complete-C candidate. O1 b=3 remains missing.

W25. task-209 decisive P is FALSE for full Out: Kondo 2025 Theorem A gives
stabilizer=finite Aut(K); H=Phi^{-1}(Sp) is infinite, so alpha in H\Aut(K)
fails some U^n. Upper numbering is not characteristic. U^e-specific
preservation is NOT proved; task-204 invalid; H_A-full/B=O_K/B=I open. The
lead-cited master 680 lines SHA 0C5A85D1... is a separate/stale pointer; use
the current ledger hash at EOF. Cited 237 lines is stale; current file 236.

W26. task-213 H=GL2 overclaim is INVALID. E34/task-216 audit
(D8B982FD...) confirms Delta/v=1/I1, #E(F7)=10/a7=-2, disc17 nonsquare/
order41, exceptional orders 24/48/120 or 480/960/2400, and SL2 containment,
but H may be SL2 itself or any larger subgroup containing it; only
SL2(F41) subset H subset GL2(F41), exact H unknown. F degree 27648 arithmetic
valid, but F2 degree24/Galois/other bad semistabilization/Galois closure
conditional; transfer to F conditional.

W27. task-217/E35 SOURCE OBSTRUCTION: Kondo F(x_i)/trace data determine the
y-basis, W=kerTr, y_i in J, diag(1,A), D fixes y1, Tr(y1) in pZ_p nonzero, but
NOT actual F(x_i), Tr(y1), c=41/Tr(y1), C, u0,w0. Models A/B/C satisfy the
recorded axioms and give H_A true/B=O_K (A,C) or H_A false/B not O_K (B). No
source selects; H_A-full_H/B_H UNDETERMINED; full H_A/B OPEN.

W28. task-218/E36 correction: H=GL2(F41) is WITHDRAWN; only SL2(F41) subset H
subset GL2(F41), H may be SL2. Certificate Delta/v=1/I1/order41/#E(F7)=10/
a7=-2/charpoly disc17 valid; exceptional 24/48/120 or 480/960/2400 41-free;
F degree 27648 conditional on F2 degree24/Galois/other bad semistabilization/
Galois closure; transfer to F conditional.

W29. task-219/E37 Kummer extraction FAILS: Kummer pairing gives only finite
order (41-torsion) noncanonical classes; Kondo x_i are pro-p wild inertia
generators and F(x_i)=log(unit) lies in J. No source identifies x_i/F(x_i)
with a Kummer dual basis, normalizes Tr(y1), or fixes C. Thus y1/Tr(y1)/c/C
remain source-undetermined; task-217 models A/B/C persist; H_A-full_H/B_H
undetermined; full H_A/B OPEN.

W30. task-222/223 underdetermination theorem SURVIVES: Model A valid
(H_A true/B=O_K); Model B H_A false valid; Model B B=I valid only with R6
(H maps onto Sp_40(Z_p), true for actual donor H=Phi^{-1}(Sp)). Identity does
NOT force B=O_K; B=I compatible since O_K subset I and other alpha images add
p^{-1}L; u0=1+pi/p in I (not outside), v_p=-40/41; B=I gap filled via
id/A=-I/p^{-1}L/Sp orbit. H_A-full=>B=O_K and contrapositive valid. H_A
underdetermination survives independently of B. Theorem as pure (R1)-(R5)
needs R6 and all-H span; B=O_K vs B=I remains undetermined.

W31. task-225 Lean C9HAFullConditional.lean (175 lines SHA 042581D6..., olean
DE05EEAA..., EXIT0/sorry0) formalizes only the abstract Qp-linear conditional
theorems: HA_full=>B=O with identity in G; 1 in U=>w0=0,a=1,HA_full,B=O;
underdetermination for w0!=0/one notin U. Caveat: exact condition is w0!=0
(one notin U), NOT U!=W^perp; trace orthogonality interface not formalized.
Not a Project/target closure; actual Kondo F/Galois data absent.

W32. task-226 Lean C9UOrthogonal.lean (148 lines SHA 656D46D2..., olean
21A71037..., EXIT0/sorry0) formalizes abstract TraceSetup: finite-dim Qp K,
nonzero Tr, W=kerTr, nondegenerate reflexive beta with beta(w,one)=0, line U;
proves one in W^perp, finrank W+1=finrank K, finrank W^perp=1,
W^perp=span{one}, U=W^perp iff one in U. Combined with C9HAFullConditional:
1 in U + one in O + O=closure({1} union J) => all a(A) in O and B=O. Caveat:
beta is abstract; multiplication x*y/actual trace pairing not formalized; not
a target closure.

W33. task-228 normalization-independent construction (314 lines SHA 6E16AA27...)
proves E_j/j0=1/p^6/v_p(Delta)=6/q=p^6+744p^12/qhat=pi^3v b=3; F degree
2,3-smooth 41-free (conditional F_sem); X_K/C_K/C_F/V/epsilon skeleton;
per-D III*/semistab4/D-part 2-power<=512; mod41 corrected 32/6 and 140/-12,
SL2 subset G subset GL2, conditional SL2 subset H; B_I-zero A_proc=11.5logpi;
conservative residual under CFTH+LB, branch-independent B=O_K weaker. No U/B
choice, no target closure.

W34. task-231 exact mod41 SUPERSEDES the E27/E31 GL2 underclaim for E_j:
exact classes #E(F7)=11/a7=-3/det7, #E(F37)=32/a37=6/det37, #E(F127)=140/
a127=-12/det4; ord_41(7)=40 so determinant full; with SL2(F41) subset G this
gives G=GL2(F41), order2,755,200. Over F, F/Q unramified at41 and
F cap Q(zeta41)=Q, determinant full; conditional on [F:Q] 2,3-smooth,
H=GL2(F41), order2,755,200. Exact F_sem degree remains conditional. Does NOT
affect E34/E36 alt-E H=GL2 withdrawal (different E, #E(F7)=10).

W35. task-233/E43 supersedes the E28/task-206 blanket "2,3 bad additive":
exact p=2 I0 good degree1; p=3 I0* additive quadratic degree2; 2,3 part of
F_sem degree=2, from p=3 only. D-prime III*/degree4 unchanged. Local p:
q=p^6u, v^82=q/p^6, qhat=pi^3v, qhat^82=q, qhat^2=q^{1/41}=pi^6v^2; qhat in
K_v (valuation3/41), NOT Q_p; e41 f1 b3. Mod41 exact G=GL2/Q, H=GL2 over F
conditional on [F:Q] 2,3-smooth. C_K/C_F/V/epsilon skeleton with psi41 degree840/
Velu/descent/global places missing.

W36. task-234/E44 exact: [F_sem:Q]=1024; F_D degree512; p=3 quadratic
absorbed in F0=Q(i,E[6]); F=Q(E[6],F_D); [F:Q]=512[F0]/[F0 cap F_D],
[F0]|576; F0 cap F_D contains Q(i), so [F] divides 147456 (or 294912 with
F_sem) and [F:Q] is 2,3-smooth UNCONDITIONALLY. E42/E43 conditional degree
hypothesis discharged; H=GL2 exact pending task-236 transport. Exact [F:Q]
still needs [F0] and F0 cap F_D.

W37. task-235/E45 psi41: modular arrays for primes 5..43, degree840, leading41,
squarefree, resultants; Velu modular t,w,A',B'. Full exact rational expansion
NOT completed (MB-scale, thousands of bits); exact rational psi41/t,w/A',B',
K equations/[K:F], C_K/C_F equations, descent, global places, cusp coords
missing. Data hashes: psi41_mod_primes.json 074096F0...,
velu_quotient_mod_primes.json 716CAEC8....

W38. task-236/E46 unconditional: [F:Q] <= 1024*576/2 = 294912 = 2^15*3^2
(intersection contains Q(i)); sharper <=147456=2^14*3^2 if contains Q(zeta12).
Hence [F:Q] 2,3-smooth and 41-free UNCONDITIONALLY. G=GL2(Q) exact; [G:H]
divides [F:Q]; PSL2(41) simple + Dickson => SL2(F41) subset H; determinant full
over F => H=GL2(F41), |H|=2,755,200 EXACT. E42/E43/E44 degree/transport
conditionals discharged for the mod41 image. Exact [F:Q] still uncomputed;
E34/E36 alt-E H=GL2 remains withdrawn.

W39. CRITICAL sign correction task-254/E47: F=Q_C-h_C; P6 h_C>=Q_C iff
F<=0. Positive F is a P6 counterexample, not positivity. B=O_K b=3:
F>=D3-A=80.550578>0 => conditional P6 counterexample if exact aligned profile
+ finite D3 + target/TC/arch inputs actual; P6 would be FALSE for that C.
B=I b=3: F=-S3-h_inf; F<0 when h_inf>-S3 is P6-HOLDING, F>0 when h_inf<-S3 is
counterexample. b=273 both branches F>0 conditional counterexamples. Truth
dichotomy: (A) actual profile => P6 false margin80.55; (B) some conditional
input fails for every C => P6 open. No third positivity reading; no
unconditional counterexample/P6 proof constructed.

W40. E48/task-265 RETRACTS W39 SIGN LOGIC: C1 is a LOWER bound on h_C, so
F=Q_C-h_C<=D-h_inf (upper bound), NOT F>=. Positive upper bound does not prove
F>0. E47's b=273 F>8821/8918 no-go and B=OK b=3 F>=80.55 counterexample are
INVALID/WITHDRAWN; task-256 b=273 no-go retracted; task-254 counterexample
reading retracted. Correct rows: b3 B=OK F<=93.714971-h_inf; b3 B=I
F<=-S3-h_inf; b273 B=OK F<=8931.174579-h_inf; B=I F<=8834.703285-h_inf. Keep
F=Q-h/P6 iff F<=0, C1/C3 residual, local arithmetic; counterexample needs
upper bound h_C<=Q-eps/TC equality. P6 open, no counterexample/proof.

## 2. Confirmed errors

### E1. TAME Section 2 symplectic donor

Error: the original C9-TAME Section 2 construction is not an actual source
theorem. Confirmed corrections from C9-SYMPLECTIC-SOURCE-20261025.md:

- rho: Mod(S minus P) -> Out(G_K) is a set-theoretic map, not known to be a
  group homomorphism; no splitting/section is known.
- The correct actual donor is the closed preimage
  H = Phi^{-1}(Sp_{2g}(Z_p)), with Phi(H) = Sp_{2g}(Z_p), not "image of rho = Sp"
  and not an explicitly split copy.
- Boundary-word-preserving free-group substitutions are not automatically
  actual Galois automorphisms. The actual source is the mapping-class/
  Dehn-twist construction rho of Kondo 2025 Section 2.
- The 2025 trace basis and the 2026 symplectic basis alignment is an inferred
  convention, not a stated cross-paper theorem.
- The trace theorem is Tr_{K/K^{(d=1)}}, not automatically Tr_{K/Q_p}; equality
  holds in the tame totally ramified case K^{(d=1)} = Q_p.
- J=m, the standard-lattice classification, orbit generation (T7), and volume
  gain (T8) are inferred consequences, not Kondo theorems.

Status: confirmed error in the original TAME Section 2; the corrected H donor
survives conditionally. Any downstream use of the original boundary-word/rho
image construction is invalid.

### E2. TAME Section 5 equations (11)-(14)

Error: (11)-(14) are not a target proof. Confirmed corrections from
C9-IND1-GLOBAL-20261025.md:

- Full Ind1 is the automorphism group of the procession
  Prc(n,circ D^dag_T), not the finite label translation of the finite model.
- A ring isomorphism F does not imply F(Hull(...)) subset H_C.
- The target-container step needs TC-A to TC-H plus TC-S.
- The row/Theta/log/gluing branch, normalized log-volume, Ind2/Ind3, and fixed
  n/infinity conditions are separate.
- The GLUING common packet transport does not by itself prove the target
  saturation needed for T14.

Status: confirmed error if (11)-(14) are used as an actual target proof; they
survive only as conditional target formulas under TC-A..TC-H/TC-S.

### E3. Task-155 B=O_K overclaim for the full finite image

Confirmed by C9-MODP-BRANCH-PROOF-20261025.md and
C9-AUDIT-BRANCH-20261025.md:

- task-155 proves an actual field-trace computation: in the pi-power model,
  Tr(pi^a)=0 for 1<=a<=40, Tr(1)=41, and W0=ker Tr; the field-trace line of
  I/J is l=O_K/J.
- The headline "B=O_K; B=I does not occur" is valid only for the preimage
  subgroup H = Phi^{-1}(Sp_40), under the inferred natural trace alignment
  U=trace line, or after adding the explicit hypothesis barGamma(l)=l.
- It is NOT a theorem for the full actual finite image barGamma. If v=0 but
  some gamma in barGamma moves l, then B=I. If v!=0, B=I. If v=0 and all
  gamma fix l, then B=O_K.
- The full branch status remains UNDETERMINED from current sources. The missing
  data are the actual W-coordinate v (or basis-alignment matrix T) and the full
  finite image barGamma on I/J.

Status: trace computation valid; conditional subgroup theorem valid; full
barGamma headline overclaim confirmed. B=I is conditional, not actual.

### E4. Task-148 target overclaims

Confirmed by C9-AUDIT-TARGET-CONTAINER-20261025.md:

- (14-u) and (15-u) are called actual/field/target hull bounds; they are
  conditional target formulas depending on the withdrawn (11)-(14) and
  TC-A..TC-H.
- h_A is called an aligned actual hull value; it is conditional target.
- branch A=O_K is called actual; B=O_K is conditional on the natural trace
  alignment and on the full barGamma fixing l, and B=I is not actual.
- h_B and the b=3 B=I surplus 9/41 are conditional branch values, not actual
  source/target values.
- The exact rational arithmetic in task-148 remains valid.

Status: invalid-as-written target claims; arithmetic values survive.

### E5. Task-151 target overclaims

Confirmed by C9-AUDIT-TARGET-CONTAINER-20261025.md:

- T7/T8 are listed as proved source orbit/hull gain; they are conditional
  inferred consequences of the corrected H donor, basis alignment,
  low-ramification J=m, standard-lattice lemma, and local naturality.
- T14/T15/H_p^Sp are used as proved target hull lower bounds; they depend on
  the withdrawn target-container step and TC-A..TC-H.
- G1/G6/G10 are conditional target assembly formulas; they are not a proof of
  h_C >= Q_C and the sign is unknown because h_infinity^actual is missing.
- The GLUING (8)-(13) common packet transport is used to justify T14 target
  containment; that is TC-B, not a proved consequence of GLUING.
- The Section 6 "proved" list must be split into valid arithmetic, conditional
  source, and conditional target categories.

Status: invalid-as-written target/proved classification; conditional assembly
survives with the corrections.

### E6. Arch b=273 branch-value label error

Confirmed by C9-AUDIT-ARITH-20261025.md:

- C9-ARCH-GLOBAL-20261025.md's b=273 row uses -38736/41 as h_p. This is the
  conditional B=I branch h_B. The B=O_K branch value is h_A=-39156/41.
- The row is invalid as a finite bad h_p label under branch A. The conclusion
  "arch-only compensation is insufficient" remains true under the correct A
  value (the deficit becomes larger: 38883/41 rather than 38463/41).

Status: confirmed label error; conclusion survives with corrected A value.

### E7. Finite model / finite test caveats

- C9-MODP-GENERATOR's e=5,p=5 model is a finite representation test, not the
  actual p>e+1 C9 field. It correctly shows trace plus Sp data alone do not
  determine l.
- The finite matrix checks in task-155 certify only the stated conditional
  matrices; they do not compute the actual line coordinate v or the full
  barGamma.
- The finite model is not a counterexample to the actual branch.

Status: no error, but any use as an actual source instantiation would be
invalid.

### E8. Archimedean radius base error (task-167)

Confirmed by task-167 / C9-RADIUS-CORRECTION-20261025.md
(SHA256 d563226d8fcde7e01f06bcddd5195f19530182f828c3b419997f78ab3188405d):

- task-156 C9-ARCH-GLOBAL A18/A19 and task-162
  C9-GLOBAL-ASSEMBLY-CORRECTED D1/D2 used the ramification index e=41 as the
  exponential base, or omitted log p entirely.
- The correct compensation formula for F=Q and one real infinite place is
  r_inf >= pi * p^{d_p}, where d_p = D_p^Sp/log p and p is the rational prime
  of the bad place, p=12301 in the concrete C9 local type.
- The number 41 is e, not the base. It appears in d_p=408/41 or 38883/41 and in
  Q_p=-b/e log p, but not in the exponential base.

Correct values:

b | d_p | D_C^Sp | required r_inf | log10 r_inf
--|----:|--------:|---------------:|------------:
3 | 408/41 | 93.7149712745967 | 1.5741451258619e41 | 41.1970447689732
273 | 38883/41 | 8931.17457860329 | 1.8071170135918e3879 | 3879.25698627470

Stale/invalid figures, withdrawn:

- task-156 A18: pi*exp(408/41) ~ 65903.669; this omitted log p.
- task-156 A19: pi*exp(38883/41); this omitted log p.
- task-162 D1: pi*41^{408/41} ~ 3.51816e16; this used base e=41.
- task-162 D2: pi*41^{38883/41} with log10 approximately 1530; this used
  base e=41.
- The earlier task-162 note that A18/A19 omitted log p was correct, but its
  replacement base 41 was still wrong; C9-RADIUS-CORRECTION supersedes that
  note as well.

Unchanged by E8: d_p=408/41 and 38883/41; B=O_K finite values -411/41 and
-39156/41; Q_p=-3/41 and -273/41; conditional B=I values 9/41 and -38736/41
(not actual under natural trace alignment); shell/positive-radius criterion;
TC-A..TC-H/TC-S. The correction is numerical only and proves no target
inequality.

### E9. Task-146 log-domain errors

Confirmed by C9-AUDIT-LOG-ARCH-20261025.md
(SHA256 F7AD81083A1772BF5A300B1B05886C28831B8BBE11BAB1B097C5A817C12547EC),
auditing C9-LOG-DOMAIN-EXTEND-20261025.md
(SHA256 CC52A8CF0D5FB56172A7AF2F6FB0C5C57EB726A5A459D3CCDE42FDDD3DAF2DFA):

- Error: task-146 claims the p-adic log diverges / converges only on U^{n0}.
  The log term on x in m^n has valuation k n/e - v_p(k); for k=p^t this is
  p^t n/e - t -> +infinity, so log converges on all U^1=1+m (indeed on m).
  The threshold n0=ceil(e/(p-1)) is the convergence threshold for exp, not for
  log. The statement that U^1/U^{n0} has no p-adic log is false for the
  power-series log.
- Error: J_K=log(O_K^times)=m^{n0} is not the full log image. It holds only for
  the restricted domain D_K=mu·U^{n0}. The full log on U^1 contains the linear
  term and is not confined to m^{n0}; J_K=m^{n0} is a source convention, not an
  analytic-domain theorem. The same remark applies to I_K=p^{-1}J_K.
- Minor error: the volume formula logvol_O(m^n)=n f/e log p = (n/e)log p drops
  the residue-degree factor f in the second equality. For f>1 only n f/e is
  correct; the tame totally ramified applications have f=1 and are numerically
  unaffected.

Valid survivors: n0=ceil(e/(p-1)); the e=p-1 boundary; exp/log inverse on the
restricted U^{n0}; exp(pz) for z in O_K; Teichmuller decomposition
O_K^times=mu x U^1; the integer lattice statement conditional on the restricted
J_K=m^{n0}; the wild-ramification warning.

Conditional: D_K=mu·U^{n0} and Teichmuller root log=0 as source conventions;
J_K=m^{n0} and I_K=p^{-1}J_K; Aut(G_K) shell preservation (TC-S/basis
alignment); wild e>p-1 analogue.

### E10. Task-150 formula/label mismatch

Confirmed by C9-AUDIT-LOG-ARCH-20261025.md, auditing
C9-ARCHIMEDEAN-20261025.md
(SHA256 F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957):

- Error: task-150 Section 4 writes TAME (10) with the term -c j,
  c=(e-1)/(2e)=20/41, but then quotes h=-411/41, which is the aligned
  (15)-value h_A=-(1/20)sum(s_j+1/41) and omits the -c j tensor-order loss.
  The actual formula-(10) value at rho=1, e=41 is

      h_10 = -(1/20)sum_j[(20/41)j+s_j+41^{-(j+1)}]
           = -210/41 - 10 - tiny
           ~= -15.122,

  not -411/41 ~= -10.024. The formula and the quoted number refer to different
  bounds. The arch-only insufficiency conclusion remains valid for the aligned
  h_A; the label "TAME (10)" must be replaced by "(15)-aligned, without -c j".
- Error: the b=273 row uses -38736/41 as a generic h_p. This is the conditional
  B=I branch, not the A=O_K branch. The corrected A value is -39156/41
  (deficit 38883/41); B=I is -38736/41 (deficit 38463/41), conditional and not
  actual under natural trace alignment. The arch-only conclusion is unchanged
  under A, but the branch label is wrong.

Valid survivors: IV archimedean container bound (j+1)log pi; procession
average (l+5)/4 log pi; dimension factor zero; sign warning between positive
paper radial volume and negative Lean readout; upper-bound-only limitation;
arch-only insufficiency for the A branch.

Conditional: b=3/b=273 finite values inherit the inferred donor/basis/orbit
generation; p_{vQ}=e normalization is paper-interface conditional; larger-b
monotonicity is an affine-period inference, not a paper theorem.

### E11. Task-156/162 archimedean normalization and radius errors

Confirmed by C9-AUDIT-ARCH-GLOBAL-20261025.md
(SHA256 7D719850564C1550D9D525EBE01AE395FE2AE5D70214F21AA83293EC73154825),
auditing C9-ARCH-GLOBAL-20261025.md
(SHA256 524E078AD85C72067627F006D165A724436E1BA508E86475C5F991860586E489)
and C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md
(SHA256 8E7EF66A737BBFE73ED13EA568875A4D1305F48D814DE4B3773BEBB3DB2F3548),
and by C9-RADIUS-CORRECTION-20261025.md
(SHA256 D563226D8FCDE7E01F06BCDDD5195F19530182F828C3B419997F78AB3188405D):

- d_v/B_I reference inconsistency: task-156 (A2) writes local
  d_v log(r/pi) but (A3) writes h_inf=sum alpha_v log(r/pi), dropping the d_v
  factor. alpha_v already contains d_v/[F:Q]; multiplying the local formula by
  d_v again would double-count the degree. Fix one convention: either
  h_v=d_v log(r/pi) and h_inf=sum alpha_v d_v log(r/pi), or h_v=log(r/pi) and
  h_inf=sum alpha_v log(r/pi).
- B_I zero-reference mismatch: task-156 cites IV Thm1.10(vii),
  log-volume(B_I)=0 and log-volume(pi^{j+1}B_I)=(j+1)log pi, but then uses
  I_v={|a|<=pi} (the shell boundary) as zero. Under IV B_I normalization a
  radial hull of radius r has log-volume log r (up to the local dimension
  convention), not log(r/pi). The shell-pi normalization is a different
  normalization. The two must not be mixed.
- Shell sign: (A9) r_v<=pi => h_inf<=0 holds only under shell-pi normalization.
  Under IV B_I normalization, r_v<=pi gives h_inf<=log pi>0, so the
  non-compensation conclusion does not follow. (A11)/(A12) product-formula
  bounds and the sign conclusion are likewise normalization-dependent.
- Radius: (A17) uses r>=pi*exp(D_C). If D_C=d_p log p, the correct
  shell-pi radius is r>=pi*p^{d_p}, not pi*exp(d_p). Task-156's numerical
  substitution pi*exp(408/41) omitted log p; task-162 D1/D2 used base 41
  instead of p=12301. E8 and C9-RADIUS-CORRECTION give the corrected values:
  b=3 r=1.5741451258619e41 (log10 41.1970447689732);
  b=273 r=1.8071170135918e3879 (log10 3879.25698627470). Under B_I
  normalization the pi factor disappears and the criterion is r>=p^{d_p}.
- Branch label: the b=273 D=38883/41 is the h_A branch value; the B=O_K h_B
  branch is 38463/41, and -38736/41 is the conditional B=I branch. The task-156
  row and downstream task-162 use of these numbers must carry the branch label.

Valid survivors: alpha_v=d_v/[F:Q], sum alpha_v=1; alpha_p finite weights;
IV container bound (j+1)log pi; dimension factor zero; product formula (A10)
as a point constraint; upper-bound-only limitation; qualitative "product
formula alone does not create positive compensation".

Conditional: h_inf formula and normalization; shell containment; necessary
radius pi factor; D_C^Sp finite residual (task-147/149); every target use
needs TC-A..TC-H/TC-S.

### E12. Task-170 log-domain correction

Confirmed by task-170 / C9-LOG-DOMAIN-CORRECTION-20261025.md
(SHA256 882DFDEF2BF11377EBC6FDC488205623804100CC54DEEACD5EC805E75F481655),
correcting task-146 C9-LOG-DOMAIN-EXTEND-20261025.md
(SHA256 CC52A8CF0D5FB56172A7AF2F6FB0C5C57EB726A5A459D3CCDE42FDDD3DAF2DFA)
and the boundary repeat in task-161 C9-AUDIT-LOG-ARCH-20261025.md
(SHA256 F7AD81083A1772BF5A300B1B05886C28831B8BBE11BAB1B097C5A817C12547EC):

- Log domain: the p-adic log converges on all U^1=1+m. The task-146 claim that
  for n<e/(p-1) the log term valuation goes to -infinity is a sign error; the
  valuation goes to +infinity. There is no log convergence threshold.
- Exp threshold: the minimal exponent is strict,
  n_exp = floor(e/(p-1)) + 1. At the integer boundary, including e=p-1,
  this is one higher than ceil(e/(p-1)). In particular e=p-1 gives n_exp=2,
  not 1; exp does not converge on m at e=p-1. The audit task-161 repeated the
  ceil boundary error.
- Restricted image: J_K=log(D_K)=m^{n_exp} only for the restricted source
  convention D_K=mu*U^{n_exp}. The full log(U^1) is larger and is not
  m^{n_exp}; do not write J_K=log(O_K^times)=m^{n_exp} as an unrestricted
  identity. The full/restricted distinction is a source-convention gap.
- Restricted shell: I_K=p^{-1}J_K=m^{n_exp-e} in convention (b); the full log
  shell is larger under convention (a).
- Volume: the residue degree f must be retained:
  logvol_O(m^n)=(n f/e)log p, not (n/e)log p. Restricted shell volume is
  ((n_exp-e)f/e)log p; the loss relative to the tame n_exp=1 is
  ((n_exp-1)f/e)log p. Task-146 omitted f; tame f=1 applications are
  numerically unaffected.

Survivors: log on all U^1; exp/log inverse on m^{n_exp}; exp(pz) safe for
every e; Teichmuller decomposition and log(mu)=0 as source convention;
integer lattice O_K+log(U^1)=O_K (restricted O_K+m^{n_exp}=O_K); same-path
h>=2 log-link empty; Kummer zero path still generates O_K; q nonunit does not
enter p-adic log.

Conditional/donor-dependent: choice of convention (a) vs (b); exact full
log(U^1) lattice for e>p-1; wild-ramification trace/symplectic replacement;
Aut(G_K) shell preservation; archimedean normalization/global weights; any
target containment TC-A..TC-H/TC-S.

E12 supersedes the task-146 log-domain statements and the task-161 boundary
sentence. It is not a target proof.

### E13. Task-173 corrected global assembly audit

E47 SIGN UPDATE: F=Q_C-h_C; P6 h_C>=Q_C iff F<=0. Positive F is a
counterexample, not positivity. E13's residual inequality F<=D_C^Sp-h_inf is an
upper bound; under the exact B=O_K aligned b=3 profile, F>=D3-A=80.550578>0,
which is a CONDITIONAL P6 COUNTEREXAMPLE if the profile/target/TC inputs are
actual. Do not read the positive 408/41 residual as positivity or P6 proof.

Confirmed by task-173 / C9-AUDIT-GLOBAL-ASSEMBLY-20261025.md
(SHA256 916DC332D9AA15D5898062EC73C3D37E56A6CA682A9411DA0470C68647E22E6B),
auditing C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md
(SHA256 8E7EF66A737BBFE73ED13EA568875A4D1305F48D814DE4B3773BEBB3DB2F3548):

- Residual formula:
  Q_C-h_C <= D_C^Sp-h_inf(C), D_C^Sp=sum alpha_p d_p log p,
  d_p=b(e+1)/12-(b-1)/e-T_p is VALID ALGEBRA but CONDITIONAL on CFTH
  (corrected donor plus TC-A..TC-H/TC-S). No complete C satisfying CFTH is
  constructed; no global closure.
- Radii D1/D2: corrected global still uses base e=41 for r_inf. This is
  INVALID. C7 requires r_inf>=pi*p^{d_p}, p=12301:
  b=3 d_p=408/41, log10(p^{d_p})=40.6998948963,
  log10(pi p^{d_p})=41.1970447690, r~1.5741451259e41;
  b=273 d_p=38883/41, log10(p^{d_p})=3878.7598364020,
  log10(pi p^{d_p})=3879.2569862747. The old 3.51816e16 and 1530.0 are
  withdrawn (see E8/E11).
- B=O_K label: natural trace alignment only proves B_H=O_K for the subgroup
  H=Phi^{-1}(Sp). It does not prove the full barGamma fixes
  l=O_K/J. The full branch is UNDETERMINED (task-153/task-160/E3); B=O_K for
  the full image requires every actual generator to fix l, i.e. an extra
  barGamma(l)=l hypothesis. The corrected global label "B=O_K under natural
  alignment" is too strong for the full image.
- Conditional b=3 residual 408/41 is conditional on barGamma(l)=l; the B=I
  value 9/41 is not actual under natural alignment. b=273 B=O_K residual
  38883/41 is conditional on the same; B=I gives 38463/41; both are positive,
  so b=273 has no closure in either branch.
- Arch procession-normalized weighted-average bound: A_arc=((l+5)/4)log pi=
  11.5 log pi~13.164394 for l=41. This is the final averaged processed bound
  from IV Thm1.10 Step(vii), NOT the raw pointwise maximal container
  ((j+1)log pi). It is a VALID CONDITIONAL bound for the averaged readout only.
  For the conditional b=3 deficit (408/41)log p~93.715 natural and b=273
  ~8931.175, A_arc excludes archimedean-only compensation for these profiles,
  but it is not a global closure and does not supply finite good-place/global
  terms. The shell branch r_v<=pi is an extra hypothesis, not a source theorem.
- Labels: d_p is dimensionless; "Q_p-H_p^Sp (log p)" headers must state log-p
  units; A_arc is natural log and needs conversion before comparison;
  "B=O_K under natural alignment" is valid only for B_H, not full barGamma;
  b=273 -38736/41 is B=I, not A=O_K -39156/41; b=3 B=I 9/41 is not actual.

No unconditional global counterexample is claimed. With F=Q_C-h_C, the exact
B=O_K aligned b=3 profile would give F>=80.55>0 (conditional counterexample if
actual); otherwise P6 remains open. Residual algebra and
the conditional closure criterion survive; all target use remains conditional
on CFTH/TC and on the full barGamma branch.

### E14. Task-165 Gamma first-column attack

Task-165 / C9-GAMMA-COLUMN-ATTACK-20261025.md
(SHA256 7BB5D789C5DFDA4CDDB9F39267D2AFCB961BBD369A2FD5983DAD2DC67378568C)
excludes the documented mapping-class and field-automorphism sources as B=I
generators, and leaves full barGamma undetermined.

Confirmed exclusions:

- Mapping-class source D fixes x_1. For odd d=2g+1, Kondo 2025 Section 2
  assigns a_i -> x_{2i}, b_i -> x_{2i+1}; x_0,x_1,sigma,tau are not hit by
  the assignment. Every mapping-class generator and every element of the
  closed subgroup D therefore fixes x_1; in the y-basis every element of D has
  first column (1,0,...,0), and y_1=F(x_1). Under the inferred basis alignment
  l=U=<y_1>, D fixes l and B_D=O_K. D cannot produce B=I unless alignment fails
  with v!=0, in which case H subset D already moves l via Sp(W)-irreducibility.
- Field subgroup Aut(K) fixes l. Field automorphisms preserve O_K,m,J,I and
  act as identity on O_K/J; they may act nontrivially on higher m-adic layers
  but fix l. A general outer conjugate alpha Aut(K) alpha^{-1} fixes alpha(l);
  if alpha(l)!=l it fixes a different line, but no source computes alpha(l).
  Kondo 2025 Theorem I gives non-normality, not generation of Out(G_K) by D and
  Aut(K); D-conjugates of Aut(K) fix l only in the v=0 alignment case.
- Explicit e=41, p=12301: every Dehn-twist generator has matrix diag(1,A) with
  A in Sp_40, first column (1,0,...,0); a W-transvection A=I+E_{2,3} also fixes
  y_1. The finite matrix I+E_{2,1} moves y_1 to y_1+y_2 and would give B=I, but
  it is not in D and not induced by the mapping-class assignment. It is a
  finite witness of the criterion, not an actual source generator.

Exact remaining question Q1:

    Is there an actual alpha in Out(G_K) (or its finite image barGamma) whose
    first column on I/J has a nonzero W-component, equivalently
    alpha(y_1)=y_1+w with w!=0?

Current status:

- D: no (fixes y_1).
- Aut(K): no (fixes l).
- D-conjugates of Aut(K): no when v=0.
- General Out elements/other actual generators: unknown; no paper computes
  their y-basis/I/J first column.

Consequences:

- Full barGamma remains UNDETERMINED. B=I is not proved realizable; B=O_K for
  full barGamma is also not proved. If Q1 is positive, B=I; if Q1 is false and
  v=0, B=O_K. If v!=0, H/D already gives B=I.
- E16 correction: the I/J first-column formulation here is type-gapped;
  y_1 in J maps to 0 in I/J, so the Kondo y-basis is not an I/J basis. E14
  survives only as a conditional k_+/alignment statement, and the
  task-153/154/155/165 B-branch statements are conditional/type-gapped.
- The b=3 B=I surplus 9/41 remains a conditional finite-matrix possibility, not
  an actual source value; the b=3 B=O_K residual 408/41 remains conditional on
  barGamma(l)=l.
- Q1 is not answered by the corrected symplectic donor alone, by
  non-normality, or by arbitrary GL_41(F_p) matrices.

E14 is an exclusion/status result, not a new target proof; no F(Hull) subset H_C
or h_C>=Q_C follows.

### E15. Task-174 canonical vs normalized norm

Task-174 / C9-CANONICAL-NORM-ATTACK-20261025.md
(SHA256 B13902F60B129135B33324E763880DA5C90B175A83E0E639293D3844DD48408B)
shows the canonical and normalized norms are not equal in general.

- Exact relation for nonzero x:
  canonical norm = (normalized norm)^d,
  log(canonical norm) = d * log(normalized norm),
  log(normalized norm) = (1/d) * log(canonical norm),
  where d=[F_v:Q_p]=relativeCompletionDegree (k:=Q)(pF S)=C7QPilotMassActual.d S.
- Equality holds only for d=1. Unramified d=f>1 still differs by f; the tame
  totally ramified C9 type has d=e=ell.
- The normalizedCompletion_norm_lt_one_iff theorem compares unit balls only; it
  does not give equality of norms or logs.
- C9Paper QPaper uses canonical localSignedLog:
  QPaper.qPilotLogVolume=localSignedLog(qCandidate)=d*PaperQLog.
  ThetaPaper uses C6 normalizedLogVolume, which is degree-normalized. Therefore
  the existing C9Paper Q<=Theta comparison mixes a canonical Q with a normalized
  Theta and is off by the factor d on the Q side unless d=1.
- Repairs: use normalized Q=localSignedLog/d in QPaperInRleq/ValuesPaper, or
  use canonical Theta=d*normalizedTheta. Do not mix conventions and do not claim
  equality. A named Lean lemma packaging log canonical=d*log normalized is
  still missing; the ingredients are present in the source files.
- Reference file: C9-CANONICAL-NORM-ATTACK-20261025.md, current 314 lines,
  SHA256 B13902F60B129135B33324E763880DA5C90B175A83E0E639293D3844DD48408B.

E15 confirms the earlier wording "canonical/normalized equality false"; it is a
normalization-convention error in any Q<=Theta comparison that mixes the two.

### E16. Task-180 full-Out y1/column type gap

Task-180 / C9-FULL-OUT-COLUMN-ATTACK-20261025.md
(SHA256 7CC2DDD03CFEFA97E38049CA1CCB90016E944DECE0185F706E42F7F97CD61FD8)
shows the earlier B-branch first-column discussion is type-gapped.

- In the tame low-ramification C9 type, every Kondo y_i=F(x_i) lies in m=J,
  hence maps to 0 in I/J=p^{-1}J/J. The y-basis is a Q_p-basis of k_+=K, not an
  F_p-basis of I/J. The phrase "alpha(y_1) has nonzero W-component in the trace
  basis of I/J" is not literally meaningful without a non-source integral
  normalization/lift.
- Kondo 2026 gives only a Q_p-linear action
  Phi: Out(G_K) -> GL_d(Q_p). The cited papers do not prove that arbitrary actual
  outer automorphisms preserve O_K, J, I, or induce an F_p-linear action on I/J.
  For arbitrary gamma, gamma(O_K) need not lie in I; the branch definition
  B=closed Z_p-span of union gamma(O_K) is therefore conditional/not well-posed
  without the integral lift.
- Mapping-class D: the k_+ statement that D fixes x_1,y_1 is correct, but its
  first column on I/J is not computed and requires the missing alignment/integral
  interface.
- Field Aut(K): actual field automorphisms preserve O_K,J,I and fix l=O_K/J;
  this part is actual. Non-normal conjugates alpha Aut(K) alpha^{-1} preserve
  alpha(O_K), not O_K; their action on O_K/J is defined only if alpha(O_K)=O_K,
  which the cited papers do not prove. Kondo 2025 Theorem I gives non-normality,
  not lattice preservation or alpha(l).
- Corrected source-conditional Q1: add the explicit hypothesis
  (H_A-full) every actual gamma in the considered full Gamma preserves O_K,J,I
  and induces an F_p-linear action on I/J compatible with the AbsTopIII/IUT III
  interface. Under H_A-full, Q1 becomes the finite first-column condition
  m_{i1}(gamma)!=0 for some i>=2; no cited source supplies the actual matrices
  beyond D/Aut(K).
- Therefore B=O_K and B=I for full barGamma are both unproved; the branch
  definition itself is conditional on H_A-full. E14's D/Aut(K) exclusion remains
  valid only as a conditional k_+/alignment statement; its literal I/J
  first-column reading is corrected by E16.

Consequences: mark task-153/154/155/165 B-branch statements as type-gapped/
conditional, not actual I/J theorems. task-155's subgroup computation and trace
table survive; the full-barGamma B=O_K/B=I claims do not. The exact remaining
gap is H_A-full plus actual full-Gamma matrices, not a missing citation.

### E17. Task-179 other local types: no positive absolute restricted shell

Task-179 / C9-OTHER-LOCAL-TYPES-ATTACK-20261025.md
(SHA256 489708DD6D1DE159036BFADD6D6484D4470A09E31B6CD97B8F81094F3B1184DB)
shows other local types do not supply a positive absolute restricted-shell
volume.

- Under task-170's strict log/exp correction, n_exp=floor(e/(p-1))+1 <= e for
  all e>=1, and I_K^{res}=m^{n_exp-e}. Therefore
      logvol_O(I_K^{res}) = ((n_exp-e) f/e) log p <= 0.
  Equality only at boundary cases (e=1 or p=3,e=2); otherwise strictly
  negative. Larger f makes the negative value more negative; f>1 cannot turn
  the absolute shell volume positive.
- The only nonnegative quantity is the normalization shift
      Delta_shell = ((n_exp-1) f/e) log p = (floor(e/(p-1)) f/e) log p,
      Delta_shell <= (f/(p-1)) log p.
  This is a shift toward zero relative to the tame n_exp=1 shell, not a positive
  output-hull theorem. No source theorem inserts Delta_shell into the complete
  C's h_C, and no actual wild/e != ell output-hull formula is supplied.
- To cover the conditional b=3 residual 408/41 log p, one would need
      f >= (p-1) * 408/41;
  for b=273, f >= (p-1) * 38883/41. f is unconstructed and has no source bound
  or actual local realization in the current corpus. A large f only makes the
  absolute shell volume (L1) more negative; Delta_shell is not actual
  compensation.
- Additional B=O_K tame bad places worsen the finite residual; B=I b=3 surplus
  12/41 is conditional/unproved, not actual. Arch A_arc~13.164 is below the
  b=3 conditional natural deficit even at p=43 (>=37.43) and far below b=273.

Impossible as source theorem: transplanting tame J=m, B=O_K/B=I, trace/W,
T14/T15 to e>=p-1; deriving actual positive h_C from Delta_shell; claiming
positive absolute restricted-shell volume from large f; using extra B=O_K bad
places to compensate; using arch max-container to close b=3/273.
Unknown: wild/e != ell actual output hull, f and actual local types, B branch,
TC-A..TC-H/TC-S, actual arch/angular, complete C.

### E18. Task-181 aggregate B=I counts: equality caveat

Task-181 / C9-AUDIT-AGGREGATE-BI-20261025.md
(SHA256 1FB1B8AB077BEB88058E9C8AF608B1D2E2C5C8E26FABBFA7F0FCE9FFCA0FD42B)
recomputes the aggregate B=I arithmetic and corrects the strictness/realizability
reading.

- Exact fixed-p constants (p=12301,e=41,l=41,m=20):
  log p=9.417435838868785, A=(46/4)log pi=13.164393687268102,
  S=(12/41)log p=2.7563226845469613,
  D3=(408/41)log p=93.71497127459669,
  D273=(38883/41)log p=8931.174578603292,
  DB=(38463/41)log p=8834.703284644149.
- Counts/ceilings:
  A/S -> 5; D3/S=34 exactly; (D3-A)/S -> 30;
  D273/S=3240.25 -> 3241; (D273-A)/S -> 3236;
  DB/S=3205.25 -> 3206; (DB-A)/S -> 3201.
- Equality caveat: N=34 gives 34S=D3 exactly, not a strict compensation. Strict
  closure needs N>=35 or h_inf>0. N=30 leaves D3-30S=11.0252907382 natural and
  can close only if actual h_inf is at least that; A is an upper bound, not an
  attained value. N=3236 leaves (4.25)S=11.7143714; N=3201 leaves the same;
  both need actual h_inf at least 11.7144.
- "Impossible under natural trace alignment" is conditional on the inferred
  basis alignment, not a paper-level impossibility. If alignment fails, B=I is
  an uncomputed conditional possibility; no actual source C realizes the
  aggregate configuration either way.
- Fixed-p repeated counts are impossible in one C because the same rational
  prime cannot occur as multiple bad places. The arbitrary-prime N=1 statement
  is abstract: existence of a prime above the threshold in the required tame
  e=41/B=I local type is not a constructed source bad place; S_bad(C) is not
  fixed by a source theorem.
- No actual C with enumerated S_bad, B=I at every place, per-p local data, actual
  h_inf, and TC-A..TC-H/TC-S is constructed. The aggregate attack is a
  conditional upper-bound exploration, not a realized complete-C configuration
  and not a global counterexample.

Withdrawn/corrected: N=34 as strict closure; unconditional "B=I impossible";
arbitrary-prime N=1 as actual bad set; A as attained archimedean value; any B=I
count as target containment or global closure.

### E19. Task-182 binding normalization decision: B_I-zero

Task-182 / C9-NORMALIZATION-DECISION-20261025.md
(SHA256 5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D)
fixes the archimedean normalization for the contradiction route.

BINDING CONVENTION: B_I-zero, from IUT IV Prop1.5(iii) and proof of
Thm1.10(vii): log-volume(B_I)=0, container pi^{j+1}B_I, bound (j+1)log pi.
This is not the shell-pi normalization.

Binding formulas:

- F=Q, radial archimedean hull: h_inf=log r_inf.
- General F: h_inf=sum_v alpha_v log r_v with alpha_v=d_v/[F:Q] and
  sum alpha_v=1; no extra local d_v factor.
- Shell containment r_v<=pi gives h_inf<=log pi=1.1447298858..., NOT h_inf<=0.
- Compensation h_inf>=D_C^Sp is r_inf>=p^{d_p} (no pi factor), for F=Q and
  one bad p with D_C^Sp=d_p log p.
- Procession-normalized weighted-average bound h_inf<=A_arc=((l+5)/4)log pi=13.164394...;
  this is the final averaged bound, NOT the raw pointwise maximal container
  ((j+1)log pi).
- Product formula h_inf>=-sum alpha_p v_p(x)log p; no -log pi term.
- Paper radial log-volume is positive; Lean sign is negative; flip when
  comparing.

Correct binding radii for p=12301, e=41:
- b=3, d_p=408/41: r_inf>=12301^{408/41}=5.0106595585e40,
  log10 r_inf=40.6998948963.
- b=273, d_p=38883/41: r_inf>=12301^{38883/41},
  log10 r_inf=3878.759836402.
The B=I b=273 value 38463/41 gives log10 3836.862885..., conditional.

Withdrawn as binding: shell-pi h_inf=log(r/pi), h_inf<=0, and
r>=pi*p^{d_p}. Those are numerically correct only for the alternative shell-pi
normalization and are NOT the paper normalization. Therefore shell-pi radii in
task-156/162/166/176 (including E8/E11 pi*p^{d_p} values) are stale as binding
numbers; E8/E11 remain valid as error analyses but their final radii are
superseded by E19. The pi factor must be removed under B_I-zero.

No global closure: residual formula B1 remains conditional on CFTH/TC-A..H/TC-S
and actual complete C.

### E20. Task-184 E16 type-gap audit of the B-branch files

Task-184 / C9-AUDIT-B-TYPEGAP-20261025.md
(SHA256 540825E769E9F2895CE2FA327719C9A5A1F46BFA751E8865CB2A16E4322BAB27)
audits task-153/154/155/165/180 under E16.

E16 type gap: y_i=F(x_i) is the p-adic log of a unit, hence y_i in m=J and
[y_i]=0 in I/J. The Kondo y-basis is a Q_p-basis of k_+=K, not an F_p-basis of
I/J. Full Out(G_K) acts only Q_p-linearly via Phi; no cited theorem proves it
preserves O_K,J,I or induces an F_p action on I/J. Therefore TAME Section 6's
full-Gamma dichotomy is INVALID AS WRITTEN; it is at best conditional under an
explicit H_A (subgroup) or H_A-full (full Gamma) integral-lift hypothesis.

Invalid as written:

- treating the y-basis as a trace-adapted F_p-basis of I/J;
- U=<y_1>=l=O_K/J inside I/J;
- H acting as diag(1,Sp_40) on I/J as an actual theorem;
- D fixes l / B_D=O_K from D fixing x_1,y_1 in k_+;
- task-155 natural alignment => B=O_K as an actual source conclusion;
- full barGamma B=O_K or B=I, and Q1 as a well-posed source question, without
  H_A-full;
- Kondo Theorem I as a B=I generator (it gives non-normality/infinite
  conjugates, not alpha(l) or lattice preservation);
- e=5,p=5 finite model as actual e=41/p=12301 evidence.

Actually proved, with no type gap:

- p=12301 prime, p=1 mod 41; K=Q_p(pi), pi^41=p; I/J has F_p-basis
  1,pi^-40,...,pi^-1; l=span(1); trace table Tr(pi^a)=0 (1<=a<=40),
  Tr(1)=41; W0=ker Tr dimension 40;
- y_i in m=J, so [y_i]=0 in I/J;
- mapping-class generators fix x_1,y_1 in k_+;
- Phi is Q_p-linear/continuous closed; H=Phi^{-1}(Sp) preimage; Sp containment;
- field automorphisms Aut(K) preserve O_K,J and fix l;
- abstract finite dichotomy given an explicit F_p action plus H_A;
- task-155 trace table and conditional subgroup statement under H_A plus the
  inferred alignment.

Status by task after E16/E20:

- task-153: UNDETERMINED verdict survives; basis-alignment matrix in
  GL_e(Z_p) is not established; type-gapped.
- task-154: local trace/linear algebra survives; full-Gamma branch proof is
  conditional algebra only; type-gapped.
- task-155: trace table/conditional subgroup B=O_K survives; full-barGamma
  headline B=O_K is invalid actual; type-gapped.
- task-165: D/Aut(K) exclusion survives only as a conditional k_+/alignment
  statement; its literal I/J first-column reading is type-gapped.
- task-180: E16 type-gap audit; invalidates TAME Section 6 as written; calls
  for H_A/H_A-full and actual matrices.

Exact missing data: H_A/H_A-full (Out action preserves O_K,J,I and acts
F_p-linearly on I/J, compatible with log-shell/unit/normalized-volume); an
integral normalization/alignment between the Kondo y-basis and a Z_p-basis of
O_K adapted to I/J; the line coordinate v or matrix T; actual first-column
matrices for generators beyond D/Aut(K); for target use TC-A..TC-H/TC-S.

No B=O_K or B=I is actual for the source; no target use is valid.

### E21. Task-186 independent audit of the normalization decision

Task-186 / C9-AUDIT-NORMALIZATION-DECISION-20261025.md
(SHA256 79384B32506BA7F1849BB140DC1C2CDF298748F569898417C0E8FEC3B7E10A6C)
independently confirms the B_I-zero binding decision, while correcting three
labels/attributions.

Confirmed binding:

- logvol(B_I)=0 (IUT IV proof Thm1.10(vii), corpus lines 1836-1859); container
  pi^{j+1}B_I has bound (j+1)log pi.
- AbsTopIII unit-ball normalization mu_k(O_k)=1, radial log-volume log r;
  shell log-volume is log pi, not 0.
- F=Q radial: h_inf=log r_inf; shell containment gives h_inf<=log pi, not 0;
  compensation radius is p^{d_p} with no pi factor.
- shell-pi survives only as an explicitly alternative normalization; it is not
  binding.

Corrected labels/attributions:

1. log10 radius vs log10 D: the printed values 40.6998948963 and
   3878.759836402 are log10 r (equivalently log10(p^{d_p}) in the shell-pi
   convention), NOT log10 D_C^Sp. The actual natural-deficit logarithms are
   log10 D_3=1.9718089764... and log10 D_273=3.9509085787...
   Any text that prints 40.699.../3878... as log10 D is wrong; it must say
   log10 radius. This is a notation/numeric error, not an error in the radius
   formula or in B_I-zero.
2. A_arc=((l+5)/4)log pi=11.5 log pi=13.164393687... is the FINAL
   PROCESSION-NORMALIZED WEIGHTED-AVERAGE upper bound of IV Thm1.10 proof
   Step(vii), not the raw pointwise maximal-container bound. The raw container
   bound is (j+1)log pi. Do not call A_arc the "maximal container" or infer
   h_inf<=A_arc for an arbitrary fixed high capsule; it is a sufficient final
   processed bound for the averaged readout.
3. D_C^Sp=d_p log p, d_3=408/41, d_273=38883/41, B=I 38463/41, and all derived
   radii p^{d_p} are CONDITIONAL on the corrected finite donor/orbit/source
   naturality/TC-A..TC-H/TC-S. They are not paper-level IV statements. The
   b=3/b=273 numbers and radii are conditional necessary values, not an actual
   constructed source radius.

Also conditional: alpha_v=d_v/[F:Q] is the F_mod=F single-radial specialization
of the IV product-normalized weights; for F=Q it is exact, for arbitrary IV
product weights it is a normalization inference. The shell radius pi is a
binding definition, but shell containment r_v<=pi is a branch hypothesis, not
a proved property of every C.

Summary: B_I-zero binding; h_inf=log r, shell<=log pi, no-pi radius formulas
conditionally correct; log10 radius/D labels, A_arc attribution, and
D_C/radius conditionality are the corrected items. E19's formulas are retained,
with the label fixes above.

### E22. Task-191 q=p^6 candidate impossible

Task-191 / C9-CONSTRUCT-E-20261025.md
(SHA256 0F4E95CD0F21921BAF93F3CC8A29BDD4BC582055B13C827D576572B74C8D422D)
refutes the task-183 q=p^6 candidate.

- q=p^6 is a rational p-adic number, hence algebraic, with 0<|q|_p=p^{-6}<1.
- The p-adic Mahler-Manin theorem (Barre-Sirieix, Diaz, Gramain, Philibert,
  Invent. Math. 124 (1996), 1-9) states: for algebraic q with 0<|q|_p<1,
  J(q)=q^{-1}+744+196884q+... is transcendental over Q.
- Therefore J(p^6) is p-adic transcendental, not rational and not algebraic.
  Treating j(p^6) as a rational j, as task-183 did, is a type error: the
  q-expansion is p-adic at q=p^6, not complex.
- Tate uniformization for an elliptic curve E/F with split multiplicative
  reduction at a place v over p gives j(E)=J(q_v). Since j(E) is algebraic,
  q_v cannot equal p^6. This holds for every number field F and every place
  over p; nonsplit multiplicative reduction reduces to the quadratic unramified
  extension and gives the same contradiction; good/additive reduction has no
  Tate parameter in this sense.
- Exact local correction (task-188): q_Tate=qhat^{2l}=pi^{246}=p^6 u^6 when
  pi^41=p u. Thus exact q=p^6 requires u=1. With u=1, q is rational and the
  Mahler-Manin contradiction applies. For u!=1, q=p^6u^6 need not be algebraic,
  the theorem does not apply, and no actual E is supplied either.
- Consequently the task-183 candidate j(p^6) rational is invalid. No E/F has
  a place over p=12301 with stable multiplicative reduction and Tate parameter
  exactly p^6. The task-191 curve profile (field of moduli Q or larger, stable
  reduction, full E[6], bad at 12301, q=p^6, mod-41 SL2) does not exist; the
  other clauses are irrelevant to the local contradiction.
- This is a proved no-go for the q=p^6 profile conditional on the cited
  p-adic Mahler-Manin theorem as a literature input. It is not a
  computation-only result; without the theorem, the exact p-adic expansion only
  gives numerical non-reconstruction, not irrationality.
- It is not a proof that no complete C exists. An actual E with a different
  local q is not constructed; O1 remains open for alternative local q, and
  complete C/S_bad/per-p types/q-BPS/gluing/target/TC-A..H/TC-S/arch remain
  missing.

Status: task-183 q=p^6 branch IMPOSSIBLE, conditional on the cited
Mahler-Manin theorem; task-183's rational j(p^6) candidate is invalid.
Alternative local q not constructed. No target containment/global inequality.

### E23. Task-193 actual E_j skeleton (q != p^6, b=3 actual)

Task-193 / C9-CONSTRUCT-KCK-20261025.md
(SHA256 E250D5C545AC6F152275B0FC9EC0E4966FF2917318D01B4C684143645C7FD40A)
constructs an actual rational-j elliptic curve skeleton, while confirming that
its Tate parameter is not exactly p^6.

Actual construction:

- p=12301, j0=1/p^6 in Q, E_j: y^2=x^3-3j0/(j0-1728)x-2j0/(j0-1728).
  This is an actual elliptic curve over Q with j(E_j)=j0.
- Delta(E_j)=2985984 p^6/(1-1728p^6)^3, and 1-1728p^6 is prime to p;
  hence v_p(Delta)=6 and v_p(j0)=-6. E_j has multiplicative reduction at p.
- The local Tate parameter is obtained by inverting j(q):
      q = p^6 + 744 p^12 + O(p^18) != p^6,
  and q/p^6 in 1+p^6 Z_p. Thus task-183's exact q=p^6 is false even for the
  rational-j curve.
- b=3 is nevertheless actual: p is prime to 82, x->x^82 is an automorphism of
  1+pZ_p, so q has an 82nd root
      qhat=q^{1/82}=pi^3 v, v in 1+pZ_p,
  with qhat^82=q and order(qhat)=3 in K_v. The local field K_v has e=41, f=1.
- F=Q(i,E[6]) is a number field, Galois over Q; #GL_2(Z/6)=288 and adjoining
  i gives [F:Q] | 576; 41 does not divide [F:Q]. E[2],E[3] are rational over F,
  i in F. K=F(E[41]) is a finite Galois extension of F.
- Formal source-level data: X_K=E_K minus origin; C_K=[X_K/E[41]] of type
  (1,41-tors)^pm; K-core C_F x_F K; V a section of bad places; epsilon the
  origin/canonical cusp. These are source-level constructions, not explicit
  equations/coordinates.
- Actual local b=3 profile with unit twist: qhat=pi^3 v with v in 1+pZ_p;
  this is the correct actual local statement, not q=p^6.

Conditional/missing:

- stable reduction of E_j over all bad places of F (2,3 and the primes of
  D=1-1728p^6), including the semistabilization extension of degree prime to
  41;
- actual q-orders at other bad places and 41 not dividing them;
- mod-41 image containing SL_2(F_41);
- explicit K equations/degree, explicit C_F/C_K/V/epsilon equations and
  coordinates;
- actual complete C satisfying all IUT I Def3.1 clauses, S_bad, per-p types,
  q/BPS/gluing, row/Theta weights, arch data, TC-A..TC-H/TC-S.

Status: O1 partial actual skeleton. Exact q=p^6 is false (E22 no-go remains
valid); the actual E_j has q=p^6+744p^12+... with the same v_p(q)=6 and b=3
local order. This does not construct a complete C and does not rescue the
task-183 q=p^6 branch. No target/global inequality.

### E24. Task-195 conditional H_A-full and B=O_K resolution

E25/E26 UPDATE: INVALID/REJECTED. task-203 verdict: task-196 is correct,
task-200 is erroneous, and E24/task-195 is invalid as written. W=ker Tr is a
Q_p-hyperplane and is NOT contained in the Z_p-lattice J; the W subset J step
is false. The corrected E26 result gives a canonical alpha_+(1)=p^{-1}alpha_+(p)
in I but does NOT prove H_A-full for full Out; B=O_K/B=I are not resolved.
The text below is the historical E24 record, not a current conclusion.

Task-195 / C9-HAFULL-ALPHA1-20261025.md
(SHA256 BA8459C4500B8E73ACFA12A3C20431C5FDF8ED1AF077DDD453F5D3C4F2E6A43B)
constructs H_A-full for full Out(G_K), conditional on H_A-lite and the Kondo
trace-kernel theorem.

Conditional inputs:

- H_A-lite from task-194 / Kondo log compatibility
  alpha_+ log = log alpha^times for full Out(G_K): every alpha preserves J,I and
  acts Z_p-linearly on J and F_p-linearly on I/J. If this is not accepted, the
  conclusions below are conditional.
- Kondo 2025 Theorem E / 1.3 trace-kernel description
  W=ker Tr_{K/K^{d=1}}=<y_2,...,y_d>_{Q_p}. With d=e=41, K^{d=1}=Q_p.

Actual local arithmetic in E24:

- K/Q_p tame totally ramified e=41, d=41, K^{d=1}=Q_p, O_K=Z_p[pi],
  pi^41=p u, J=m, I=p^{-1}J.
- Tr(pi^a)=0 for 1<=a<=40, Tr(1)=41; W=ker Tr=span(pi,...,pi^40), dim 40,
  W subset J. The Kondo y-basis is not used as an I/J basis (E16 respected).
- Out(G_K) compact/profinite; Q_p^times=p^Z x Z_p^times.
- Field automorphisms sigma(pi)=zeta pi have alpha_+(1)=1, lambda=1,w=0.

Conditional construction:

- Since the trace-kernel description is group-theoretic, alpha_+(W)=W for all
  alpha in Out(G_K). Hence Tr o alpha_+ and Tr have the same kernel W, and
  there is a unique lambda(alpha) in Q_p^times with
      Tr o alpha_+ = lambda(alpha) Tr.
- alpha -> lambda(alpha) is a continuous homomorphism Out(G_K)->Q_p^times;
  compact image lands in Z_p^times. Thus lambda(alpha) in Z_p^times.
- Write alpha_+(1)=c(alpha)1+w(alpha), w in W. Applying Tr gives
  c(alpha)=lambda(alpha); hence
      alpha_+(1)=lambda(alpha)1+w(alpha), lambda in Z_p^times,
      w in W subset J,
  so alpha_+(1) in Z_p+J=O_K.
- Using alpha_+(J)=J and O_K=Z_p1+J, alpha_+(O_K) subset O_K. Apply to
  alpha^{-1} to get the reverse inclusion; therefore alpha_+(O_K)=O_K for all
  alpha in Out(G_K). This is H_A-full, conditional on H_A-lite and the
  trace-kernel theorem.
- Consequently gamma(O_K)=O_K, gamma(J)=J, gamma(I)=I for all gamma in
  Out(G_K), and
      B=closed Z_p-span union_gamma gamma(O_K)=O_K.
  B=I is excluded. The conditional b=3 B=I surplus 9/41 is NOT selected; the
  B=O_K finite value 408/41 is the relevant conditional value. The line l is
  stable: alpha_+(1) mod J=lambda(alpha) mod J is nonzero.

Status and limits:

- B branch: RESOLVED CONDITIONAL, B=O_K for full Out, under H_A-lite plus the
  Kondo trace-kernel theorem. This supersedes the E16/E20 type-gap status only
  conditionally: without H_A-lite, the full integral action is still missing and
  E16/E20 stand. The E16 invalid literal y-basis/IJ reading is not restored.
- Not actual: a source-level proof of H_A-lite for all Out(G_K); explicit
  matrices/lambda(alpha)/w(alpha) for generators beyond the field subgroup; an
  actual complete C, S_bad, q/BPS/gluing, row/Theta weights, arch h_inf,
  TC-A..TC-H/TC-S; no global h_C>=Q_C or target containment.
- b=3 B=I branch excluded conditionally; do not use 9/41 as an actual surplus.
  The B=O_K residual 408/41 remains conditional on the finite donor/TC inputs.

### E25. Task-203 verdict: task-196 correct, task-200 erroneous, E24 invalid

FINAL ADJUDICATION: task-196 is correct; task-200 is erroneous; E24/task-195
is invalid as written. task-196's W=ker Tr Q_p-hyperplane/non-subset-J point
controls. task-200's W=span(pi..pi40)⊂J reading is rejected. E24's W subset J
step is false. E26 supplies the corrected canonical alpha_+(1) formula; it does
not prove H_A-full for full Out. The task-196 position below is binding; the
task-200 position is retained only as the rejected audit record.

Task-196 rev5 / C9-AUDIT-HAFULL-LITE-20261025.md
(SHA256 EF755618B74DC45913A6DD148E1E60ABC97CB6C4188748AC6F907EF9305FF223)
rejects the E24 H_A-full argument.

Alleged error in E24:

- W=ker Tr is a Q_p-hyperplane of dimension 40 in K, while J=m is a Z_p-lattice
  of rank 41 in K. A nonzero Q_p-vector space cannot be contained in a
  Z_p-lattice. For example p^{-1}pi lies in W but not in m=J.
- The correct integral intersection is W cap J=Z_p-span(pi,...,pi^40), which is
  strictly smaller than W. E24 used "w(alpha) in W subset J", and this
  inclusion is false.
- Therefore the formal decomposition alpha_+(1)=lambda(alpha)1+w(alpha) with
  w in W does not imply alpha_+(1) in Z_p+J=O_K. The conclusion
  alpha_+(O_K) subset O_K and its inverse equality fail.
- Consequently B=O_K is NOT proved for full Out, and B=I is NOT excluded. The
  b=3 B=I 9/41 branch is not selected, but B=O_K is also not selected; the B
  branch is UNDETERMINED/type-gapped again.

Valid conditional survivors from E24/task-195:

- alpha_+(W)=W (group-theoretic kernel preserved).
- Tr o alpha_+ = lambda(alpha) Tr.
- lambda(alpha) in Z_p^times by compactness.
- The formal decomposition alpha_+(1)=lambda(alpha)1+w(alpha), w in W, is
  correct as a Q_p-linear decomposition; only the false W subset J consequence
  fails.
- Actual local trace table, W=ker Tr=span(pi,...,pi^40) over Q_p, field
  automorphism sigma(pi)=zeta pi with lambda=1,w=0, and the compactness argument
  survive.

Invalid/withdrawn:

- E24 as H_A-full; task-195 final construction; full Out preserves O_K/J/I;
  B=O_K, B=I excluded; task-153/154/155/165/180 "conditionally resolved"
  B branch. These revert to UNDETERMINED/type-gapped pending a correct
  integral-lattice/alpha_+(1) argument.
- Do not use the b=3 B=O_K 408/41 as selected; do not use B=I 9/41 as actual
  surplus. Both branches remain conditional/undetermined.

Status of task-196 position: non-binding until task-203. It alleges that
W=ker Tr is a Q_p-hyperplane, not a subset of the Z_p-lattice J, so alpha_+(1)
need not lie in O_K; if correct, E24 is invalid and B=O_K/B=I remain
undetermined.

Task-200 position (REJECTED by task-203; retained as erroneous audit record):

Task-200 / C9-AUDIT-HAFULL-ALPHA1-20261025.md
(SHA256 8B63FF614DE6E3E041C850C5AB829D60EE376A7EF622176A9760F97D0A9D80A6)
says the task-195/E24 construction passes the structural audit:
- W=ker Tr=span(pi,...,pi^40) subset J;
- alpha_+(W)=W via the Kondo group-theoretic trace kernel;
- Tr o alpha_+=lambda Tr; compactness gives lambda in Z_p^times;
- alpha_+(1)=lambda 1+w with w in W subset J, so alpha_+(1) in O_K;
- alpha_+(O_K) subset O_K and inverse gives equality;
- hence H_A-full for full Out and B=O_K, B=I excluded; b=3 B=I 9/41 withdrawn.
It classifies dependencies as Kondo 2026 Theorem2.6 proof log diagram, Kondo
2025 Theorem E/1.3 trace kernel, Out compact/profinite, standard
reconstruction, and no circular B assumption.

Adjudication questions for task-203 (not resolved here):
1. Is W=ker Tr defined as a Q_p-subspace or as the Z_p-lattice span(pi..pi40)?
2. Is K=Q_p1 direct-sum W valid with W a Q_p-hyperplane? Then can W be a
   subset of m=J, a Z_p-lattice?
3. Does the Kondo trace-kernel description give a Q_p-basis or an integral
   Z_p-lattice? Does alpha_+(1) lie in O_K?
4. Which audit's W definition is correct, and is E24 valid?

FINAL LEDGER STATUS after task-203: E24/task-195 INVALID; task-196 correct;
task-200 erroneous. E26 gives the corrected canonical alpha_+(1) and exact
criterion, so:
- H_A-lite is conditional/valid on the paper interface; alpha_+(1)=p^{-1}
  alpha_+(p)=p^{-1}log(alpha^times(exp p)) in I is canonical;
- H_A-full(alpha) iff a(alpha)=alpha_+(1) lies in O_K minus J; under H_A-full,
  B_Gamma=O_K and B=I cannot occur;
- H_A-full for full Out/Gamma_0=Out is NOT proved; exact obstruction is the
  integrality of a(alpha)/explicit alpha_+(p) or alpha^times(exp p);
- B=O_K is CONDITIONAL on H_A-full; B=I is not available under H_A-full and not
  constructed outside it; b=3 B=I 9/41 is not selected; b=3 B=O_K 408/41 is
  conditional, not actual;
- E16/E20 remain binding for the y-basis/IJ type gap and missing full integral
  action.

### E26. Corrected alpha_+(1) and H_A-full criterion (task-202)

Task-202 / C9-HAFULL-CORRECTED-ATTACK-20261025.md
(SHA256 A1BDFD61B7FB90D1D24EC9A3D770C308360A095F435D4A2C9F35509775356BF0)
gives the corrected construction and exact criterion after the E24 rejection.

- Binding corrections: E16/E20 (y-basis not an I/J basis; full Out only
  Q_p-linear; H_A/H_A-full source hypotheses), E24 invalid at W subset J,
  task-203 verdict task-196 correct/task-200 erroneous.
- H_A-lite (conditional on reciprocity/Kondo/AbsTopIII): every alpha preserves
  J and I, acts Z_p-linearly on J and F_p-linearly on I/J. Does not imply
  O_K preservation.
- alpha_+(1) IS determined by H_A-lite:
      a(alpha)=alpha_+(1)=p^{-1}alpha_+(p)
             = p^{-1}log(alpha^times(exp p)) in I=p^{-1}J.
  This is canonical; it uses p^{-1}p and the action on J, not an arbitrary lift
  or the trace decomposition. The earlier "alpha_+(1) is undetermined" is false.
- Exact criterion:
      H_A-full(alpha) <=> alpha_+(O_K)=O_K
                       <=> a(alpha) in O_K minus J.
  Equivalently, in a=lambda 1+w, w must lie in J cap W (integrality), not
  W subset J. The E24 identity W subset J is never used.
- Conditional theorem:
      H_A-full for all actual alpha => every alpha fixes l=O_K/J
                                   => B_Gamma=O_K.
  Proof: if a in O_K, write a=lambda 1+w; w=a-lambda1 lies in O_K cap W=J cap W,
  so w in J; modulo J, a=lambda1 with lambda nonzero. B=I cannot occur while
  H_A-full holds.
- H_A-full for full Out/Gamma_0=Out is NOT proved. Exact obstruction: the
  integrality of a(alpha) in O_K minus J, equivalently explicit alpha_+(p) or
  alpha^times(exp p); Gamma_0=Stab(O_K) is only open finite index, Gamma_0=Out
  not proved. No cited source computes these for full Out generators.
- Abstract counterexample: U(p)=pi, U(pi)=p, U(pi^a)=pi^a (2<=a<=40) preserves
  J,I (H_A-lite) but U(1)=p^{-1}pi not in O_K, so U is not H_A-full. This shows
  H_A-lite does not force H_A-full; U is not asserted to be in Phi(Out(G_K)).
- B branch: B=O_K is conditional on H_A-full; B=I is not available under
  H_A-full and not constructed outside it. b=3 B=I 9/41 is not selected; b=3
  B=O_K 408/41 is conditional on H_A-full/finite donor/TC, not actual.
- Not constructed: explicit alpha_+(p)/alpha^times(exp p)/matrices for full Out
  generators, Gamma_0=Out proof, complete C, S_bad, q/BPS/gluing, row/Theta
  weights, arch h_inf, TC-A..TC-H/TC-S; no target containment/global h_C>=Q_C.

E26 supersedes the "alpha_+(1) undetermined" reading of E25's task-196 audit.
E25's lattice rejection of E24 remains binding; E26 is the corrected route, not
a revival of E24.

### E27. Task-210 mod-41 image audit: GL2 claim invalid, SL2 survives

E42 UPDATE (task-231): this E27 GL2-underclaim is SUPERSEDED for E_j by the
additional exact l=7 class (det7 order40), which makes the determinant full and
restores G=GL2(F41). E27's exact two-class counts/orders and its statement that
the two available classes do not prove GL2 remain correct; the final E_j G is
GL2. The alternative-E E34/E36 GL2 withdrawal is separate and unaffected.

Task-210 / C9-AUDIT-MOD41-IMAGE-20261025.md
(SHA256 834873837713EEE9AFA9E056E6B5682FA6D00DFE391322B8DC3B97677F8998D3)
corrects task-205 C9-MOD41-IMAGE-20261025.md
(SHA256 993DE815B8442E2F44CC39877E597F7BD474180234EABE5EF4AE27DF25BBF21F).

Numerical corrections:

- #E(F_37)=32 and a_37=6, not #E=44/a_37=-6. The file used the Legendre sum
  with the wrong sign convention.
- #E(F_127)=140 and a_127=-12, not #E=116/a_127=12.
- The wrong values are the negatives of the true traces; the projective-order
  data are unchanged because Delta depends on t^2.

Correct projective/determinant data:

- l=37: Delta_37=11 nonsquare, projective order 7; determinant 37 has order 5
  in F_41^times, NOT 40.
- l=127: Delta_127=5 square, projective order 5; determinant 4 has order 10.
- The determinant subgroup generated by these classes has order lcm(5,10)=10,
  not 40 and not all of F_41^times. Therefore GL2(F_41) (order 2,755,200) is
  NOT proved. Correct conclusion: SL2(F_41) subset G subset GL2(F_41), G
  transitive on nonzero vectors, determinant image contains an order-10
  subgroup; exact G/determinant image not determined by the displayed data.

What survives:

- Dickson maximal-subgroup index list 42,861,820,114800,57400,22960;
- the l=37 projective order 7 excludes Borel/split Cartan/exceptional;
- the l=127 projective order 5 excludes nonsplit Cartan;
- hence SL2(F_41) subset G over Q. This uses discriminants/projective orders,
  not the wrong traces or determinant fullness.

Transfer to F:

- The task-205 passage used G=GL2 and full determinant; this is invalid.
- The conclusion can be repaired using only SL2(F41) subset G plus
  [F:Q] 2,3-smooth: [G:H] divides [F:Q], and all maximal-subgroup indices
  missing SL2 contain 5 or 7, so H contains SL2(F41).
- The transfer is conditional on [F:Q] being 2,3-smooth. E[6] and i
  contributions are actual 2,3-smooth; the semistabilization degree F_sem is
  conditional/missing. If F_sem contributes 5 or 7, the transfer is not
  justified and the F-image must be computed directly.
- Exact H order over F and determinant image over F remain missing.

Marked invalid from task-205: GL2(F41) over Q, order 2,755,200, full
determinant, and the G=GL2-based transfer. Marked valid/conditional: SL2
containment over Q and the repaired 2,3-smooth transfer. The displayed data do
not prove G=GL2; do not cite task-205's GL2/2,755,200 claim.

### E28. Task-206 per-D Kodaira types and F_sem degree

E43 UPDATE (task-233 exact): the blanket "2,3 bad additive" in E28/task-206 is
SUPERSEDED. Exact: p=2 is I0 good (degree1); p=3 is I0* additive (quadratic
semistabilization degree2); the 2,3 part of F_sem degree is 2, from p=3 only.
The D-prime type III*/local degree4 part of E28 stands. Final V_bad is {p=12301}.

Task-206 / C9-DPRIMES-KODAIRA-20261025.md
(SHA256 DA7DFD3137E0D0287403390DAEE4039F5681648748E0366FF8D7A0A8A382AC70)
computes the per-D local types and corrects the task-198 2,3 statement.

Actual/exact per-D results:

- D=1-1728p^6=-1009*50833*1799579*64860221162029 is squarefree.
- For every q|D, the minimal model has
  (v_q(c4),v_q(c6),v_q(Delta))=(3,5,9), which is Kodaira type III* (not I3*).
- Each q|D has local semistabilization degree 4 (quartic ramified q^{1/4};
  degrees 1,2,3 do not make Delta a unit). Exact scaling proof.
- D-part global semistabilization degree is a 2-power and <=4*4*4*8=512
  (three q=1 mod4 quartic cyclic; q=1799579=3 mod4 has Galois closure degree 8
  containing i). Exact global degree is NOT determined; only the 2-power bound
  and 41 not dividing are established.

Correction to task-198 (C9-EJ-COMPLETION, SHA
08F308CD1F656520BE3668B0C62776BA8CD38AFB66A34C7BD5522696BC7EA226):

- task-198 said E_j is good at 2,3. This is FALSE. Both are bad additive:
  at q=2, y^2=x^3+x is singular over F_2; at q=3, y^2=x^3+1 is singular over
  F_3. Exact Kodaira types/local degrees at 2,3 are not computed, but their
  semistabilization degrees only involve 2,3 and cannot introduce 41.
- After F_sem (D-primes plus 2,3 semistabilization), D-primes and 2,3 become
  good; p=12301 remains multiplicative I_6. Thus V_bad={p} after F_sem; no other
  bad q-orders; p has qhat order b=3 independent of the unit twist.
- F_sem total degree is 2,3-smooth and 41 does not divide it; exact global
  degree remains missing (need field intersections/explicit local fields).

Other actual data: p=12301 prime, D factorization, 2985984=2^12*3^6, p type
I6, b=3; F=Q(i,E[6],F_sem) degree 2,3-smooth, 41 not dividing (conditional on
the semistabilization fields). Missing: exact 2,3 Kodaira types/degrees, exact
global F_sem degree, explicit local/global field equations, mod-41 image,
explicit C_F/C_K/V/epsilon, complete C and target data.

### E29. Task-197 alternative actual E profile with b=1

Task-197 / C9-ALTERNATIVE-E-PROFILE-20261025.md
(SHA256 6E231A5D7EB23B8ACBB78E8FAEB21C6C3C8733829955628719CE1CBB8CD5A5AC)
constructs an actual alternative E over Q with split multiplicative reduction
at p=12301 and v_p(q)=1, hence the alternative b=1 local profile.

Actual data:

- E: y^2=x^3+4x-2437249 over Q.
- Delta(E)=-2566158921220528=-16*12301*19*686229757.
- j(E)=442368/160384932576283=442368/(12301*19*686229757).
- Bad-reduction set over Q: {2,19,12301,686229757}.
- At p=12301: split multiplicative reduction, v_p(Delta)=1, v_p(j)=-1.
- At 19 and 686229757: multiplicative reduction, v=1, stable.
- At 2: additive with v_2(Delta)=4, but v_2(j)=14>=0, potential good after a
  2-power extension.
- Actual Tate parameter: q has v_p(q)=1, q=p*(5348+1516p+7385p^2+...),
  q/p in Z_p^times; q is not p^6 (valuation 1 vs 6), not a Mahler-Manin
  counterexample. Newton residual J(q)-j(E) is 0 mod p^20; an actual q modulo
  p^21 is displayed in the source but not needed as a closed value.
- F0=Q(zeta_12,E[6]) is Galois over Q, degree divides 4*|GL2(Z/6)|=1152=2^7*3^2,
  hence 41 does not divide [F0:Q]; full E[6] rational over F0.
- Strict F=Q(zeta_12) FAILS for this curve: the cubic x^3+4x-2437249 has
  nonsquare discriminant, so Q(E[2]) is an S3-extension and cannot lie in the
  abelian Q(zeta_12). The actual F must be larger than Q(zeta_12), allowed by
  IUT I Def3.1(b) (F/F_mod Galois degree prime to l). If the strict
  Q(zeta_12) version is required, this curve is not a solution and the search
  for an abelian E[2]/E[3] curve remains open.
- The curve is constructed by solving the exact congruence 4a^3+27b^2=0 mod
  p for a=4 and choosing b with squarefree quotient/split node; the bad set and
  q are computed, not selected.

Alternative profile:

- b=1 local order (v_p(q)=1), not b=3; qhat in the appropriate 82nd-root
  normalization gives order 1 (the local q has valuation 1 and q/p a unit).
  This is the alternative local q contemplated after E22/E23; it does not
  restore q=p^6 and does not select B=I/B=O_K.
- F0 degree is 2,3-smooth and 41 not dividing; F2 part is 2-power.
- Missing/conditional: exact F0 degree, semistabilization at 2/19/686229757
  over F, explicit F equations, complete C, V_bad, q/BPS/gluing, TC-A..TC-H/
  TC-S, mod-41 image, target/global data. No complete C and no P6 proof.

Status: actual alternative E with b=1 profile; strict Q(zeta12) fails; larger
Galois F allowed; O1 partial. Not a target proof.

### E30. Task-208 unit filtration audit: task-204 premise false

Task-208 / C9-AUDIT-UNIT-FILTRATION-20261025.md
(SHA256 8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09)
refutes the central premise of task-204 / C9-HAFULL-INTEGRALITY-20261025.md
(SHA256 16523153A35BF386899AC2F36EB6DB53C777F7CA704034615646BD84DF002929).

- Kondo 2025 Theorem A: the subgroup of Out(G_K) preserving the upper
  ramification filtration is exactly the finite field-theoretic subgroup
  Aut(k). It is NOT all of Out(G_K). The upper filtration is not characteristic
  in the abstract profinite group.
- The corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)) is infinite while Aut(k) is
  finite; choose actual alpha in H minus Aut(k). By Theorem A, alpha does not
  preserve the upper filtration; for some unit level n,
  alpha^times(U^n) != U^n. Kondo 2025 Theorem B gives a second independent
  actual obstruction.
- Therefore task-204's step "alpha^times(U^n)=U^n for all alpha" is FALSE, and
  the conclusion alpha^times(exp p) in U^e fails; a(alpha)=p^{-1}alpha_+(p)
  need not lie in O_K.
- Valid task-204 local parts: pi^e=p u, U^e=1+pO_K, exp p in U^e, log U^e
  subset pO_K, p^{-1}log U^e subset O_K; Kondo log compatibility
  alpha_+ log=log alpha^times is paper-level valid for all alpha;
  a(alpha)=alpha_+(1) is canonical/conditional.
- Invalid task-204 conclusions: a(alpha) in O_K for all Out; H_A-full for full
  Out; B=O_K for full Out; B=I excluded for full Out. Only the field-theoretic
  subgroup Aut(k) (and the finite-index Gamma_0=Stab(O_K) subgroup where
  applicable) gives H_A-full / B_Aut(k)=O_K. Full H_A-full and the full B branch
  remain OPEN; B=I is not selected and B=O_K is not proved for full Out.

Status: task-204 conditional INVALID; B branch OPEN; E26's canonical formula
survives but its H_A-full criterion is not met for full Out.

### E31. Task-211 mod-41 correction 2: GL2 claim superseded, SL2 transfer repaired

E42 UPDATE: the two-class subgroup really is det^{-1}(<37,4>) order688,800,
so this E31 underclaim is correct for l=37/127 only. The exact l=7 determinant
(det7 order40) is the missing element; with it, E_j has G=GL2(F41) and, over F
conditionally, H=GL2(F41). Task-205's old GL2 conclusion is restored only via
E42's correct data.

Task-211 / C9-MOD41-IMAGE-CORR2-20261025.md
(SHA256 78FD8184AD13DC1C1DFCB2BDB90A7B92A5ECE737A6B92F83945844AEBF727140)
supersedes task-205's GL2 claim and repairs the transfer to F.

Corrected exact data:

- #E(F_37)=32, a_37=6; #E(F_127)=140, a_127=-12. The old values
  44/-6 and 116/12 were sign errors.
- l=37: Delta=11 nonsquare, projective order 7.
- l=127: Delta=5 square, projective order 5.
- ord_41(37)=5, not 40; ord_41(4)=10. The determinant subgroup generated is
  order lcm(5,10)=10, not full F_41^times.
- Therefore G=GL2(F41), order 2,755,200, is NOT proved. Correct:
      SL2(F41) subset G subset GL2(F41),
      |SL2|=68,880, |GL2|=2,755,200, G transitive,
      determinant image contains an order-10 subgroup;
  exact |G|/determinant image undetermined.
- The Dickson exclusion and SL2(F41) subset G over Q survive; they depend only
  on the corrected discriminants/projective orders.

Repaired transfer to F:

- Let G=image(G_Q), H=image(G_F); F/Q Galois gives H normal in G and [G:H]
  divides [F:Q].
- If H misses SL2, then K=H cap SL2 is a proper normal subgroup of SL2
  (PSL2(41) simple), so K is 1 or {+-I}; then [G:H] is divisible by
  68,880 or 34,440, hence by 5 or 7.
- But [F:Q] is 2,3-smooth (conditional on the E_j completion/semistabilization
  degree), contradiction. Therefore SL2(F41) subset H.
- This repair uses only SL2 subset G, normality, simplicity of PSL2(41), and
  [F:Q] 2,3-smooth; it does not use G=GL2 or determinant fullness. If [F:Q]
  contains 5 or 7, the transfer is not justified and H must be computed directly.

Superseded from task-205: exact GL2 claim, order 2,755,200, determinant
fullness, and the G=GL2-based transfer. Valid: corrected point counts/traces,
projective orders 7/5, SL2 containment, conditional 2,3-smooth transfer.
Missing: exact |G|/|H|/determinant, explicit Frobenius matrices, actual [F:Q]
and F_sem degree verification, full C/TC/BPS/Theta/gluing.

### E32. Task-212 alternative E completion: I_1/b=1/2, not C9 b=3

Task-212 / C9-ALT-E-COMPLETION-20261025.md
(SHA256 C991A8C3C8752E0908F46843583A8509F0259A33C6E1FC8C195CB93E18EEDD85,
139 lines; supersedes the stale ad3614b2 pointer)
builds a source-level completion skeleton for the alternative E and checks the
local C9 hypotheses.

Actual local data:

- E: y^2=x^3+4x-2437249 over Q; Delta=-16*12301*19*686229757;
  j=442368/(12301*19*686229757).
- At p=12301: split multiplicative, v_p(Delta)=1, v_p(j)=-1, reduction I_1.
  The Tate parameter has v_p(q)=1, not 6.
- Formal TAME exponent from q=pi^{2bl}: b=41*v_p(q)/(2l)=41/(2*41)=1/2, not an
  integer 3. The 2l=82 root qhat=q^{1/82} has valuation 1/82 and is not an
  integral power of the local uniformizer. In the E[41]-field K_v,
  q^{1/41}=pi is a uniformizer, but qhat=pi^{1/2} is not in K_v.
- Therefore the C9 local hypotheses e=41, f=1, b=3, q=p^6u^6 FAIL at p. The
  actual local type is I_1, not the b=3/I_6 profile.
- At 19 and 686229757: v(Delta)=1, multiplicative I_1, stable; v(q)=1, no
  integer b=3. At 2: additive potential good (v_2(Delta)=4, v_2(j)=14>=0),
  good after a finite 2-power extension F2. No other bad primes.

Def3.1 skeleton status:

- (a) F contains i (F0=Q(zeta_12,E[6]) contains zeta_12).
- (b) stable reduction after F=F0F2; field of moduli Q; F/Q Galois degree
  prime to 41; full E[6] over F0 subset F. Satisfied at source-skeleton level;
  F2 is 2-power and F0 degree is 2,3-smooth, so 41 does not divide [F:Q].
- (c) K=F(E[41]) exists; l=41 is prime to residue characteristics of
  {19,686229757,12301}; but SL2(F41) image is NOT verified, and the p
  q-order/b=3 C9 hypothesis fails. Conditional (image) and false (b=3).
- (d)-(f) C_K=[X_K/E[41]] type (1,41-tors)^pm, C_F, V section over bad rational
  primes {19,686229757,12301}, epsilon origin/canonical cusp are source-level
  defined; explicit equations/stacky points/cusp coordinates missing.

Verdict: the actual E admits a valid alternative complete-C candidate with
local type I_1, but it is NOT a C9 b=3 complete C. It cannot feed the b=3
compensation formulas. The b=3 O1 construction remains missing. No arbitrary
curve/local parameter was introduced; the mismatch is a negative result from
the actual E.

### E33. Task-209 decisive P: principal filtration not preserved by full Out

Task-209 / C9-PRINCIPAL-FILTRATION-P-20261025.md
(SHA256 F125420F44405B360A289CDF1787C6C4F979D122EB6E65072639DF1B6E160599,
236 lines in the current file; the cited 237-line count is stale)
refutes P: full Out(G_K) does NOT preserve the principal unit filtration
U^n=1+m_K^n, in particular not U^e=1+pO_K for e=41.

- Kondo 2025 Theorem A: the stabilizer of the upper ramification filtration is
  exactly the finite field-theoretic Aut(K) subset Out(G_K), not all Out.
  Condition (3) is the upper-numbering compatibility.
- Corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)) is infinite; Aut(K) is finite, so
  choose alpha in H minus Aut(K). Theorem A gives some upper G_K^u not preserved;
  under local reciprocity some principal unit group U^n is not preserved, hence
  alpha^times(U^n)!=U^n. This is an actual source-based counterexample.
- Kondo 2025 Theorem B gives a second independent actual counterexample phi.
- The upper numbering is canonical relative to K but not characteristic in the
  abstract profinite G_K; inertia/wild inertia are characteristic but higher
  upper ramification subgroups are not.
- P as the all-n/all-Out statement is FALSE. The narrower statement
  alpha^times(U^e)=U^e for all alpha is NOT PROVED; Theorem A only gives some
  level n. Task-204 used exactly this unsupported U^e-specific preservation.
  Therefore task-204 is invalid for full Out.
- Consequences: H_A-full for full Out NOT PROVED; B=O_K for full Out NOT PROVED
  (conditional on H_A-full); B=I NOT excluded and not constructed; only
  Aut(K) and the finite-index Gamma_0=Stab(O_K) subgroup results are conditional.
  The canonical alpha_+(1) formula and the criterion
  H_A-full(alpha) iff a(alpha)=alpha_+(1) in O_K minus J survive; the open
  obstruction is integrality, not determination.
- Valid local facts: exp(p) in U^e, log U^e subset pO_K, p^{-1}log U^e subset
  O_K, alpha_+ log=log alpha^times, a(alpha)=p^{-1}log(alpha^times(exp p)) in I.
  Missing: alpha^times(U^e)=U^e for all alpha; hence a(alpha) in O_K is not proved.

Status: P FALSE full Out; task-204 invalid; H_A-full/B=O_K/B=I OPEN; canonical
a(alpha) in I and integrality criterion survive. Lead-cited master pointer
680 lines SHA 256 0C5A85D1A72E8F64F2CE92178261C81480A0D323C1FD24CF11CF75FDC953B4B1
is a separate/stale pointer; current ledger hash is recorded at the end of this
file and must be used for ledger identity.

### E34. Task-216 audit: alternative E SL2 valid, H=GL2 invalid

Task-216 / C9-AUDIT-MOD41-ALT-E-20261025.md
(SHA256 D8B982FD1F99C5F0147ABD3BE3333A8254E7F1F1977063DA9A0F6511F320E9CA)
audits task-213 / C9-MOD41-ALT-E-20261025.md
(SHA256 EB8CD3705E46AA800F99E14C974FF0EF70FB3E38F62D3CE44C22A8F044C70971).

Confirmed actual:

- Delta=-2^4*19*12301*686229757; v_p(Delta)=1; minimal model; v_p(j)=-1
  => multiplicative type I_1 at p=12301.
- #E(F7)=10, a_7=-2; charpoly x^2+2x+7 mod41 has disc 17; 17^20=-1 mod41,
  so 17 is nonsquare and the l=7 Frobenius is irreducible.
- I_1 inertia gives a nontrivial unipotent of order 41 in the mod-41 image H.
- Dickson: the non-Borel maximal subgroups not containing SL2 have orders
  65600 (Borel), 3200 (split Cartan normalizer), 3360 (nonsplit Cartan
  normalizer), or exceptional binary polyhedral orders 24,48,120 (scalar
  preimages 480,960,2400). All non-Borel orders are prime to 41; the
  irreducible element excludes a Borel. Hence SL2(F41) subset H is VALID.
- Exceptional order list in task-213 was imprecise (projective order times
  scalar center is not the exact maximal-subgroup order), but all orders are
  41-free, so the SL2 exclusion argument is unaffected.

Invalid overclaim:

- H=GL2(F41) is NOT proved. The maximal-subgroup list used in task-213 omits
  the proper subgroups that contain SL2, notably SL2(F41) itself. SL2(F41) is
  proper, contains the order-41 unipotent and irreducible l=7 element, is not
  in a Borel/Cartan normalizer/exceptional subgroup, and is not GL2. Therefore
  the correct conclusion is
      SL2(F41) subset H subset GL2(F41),
  with H possibly SL2 or larger; exact H and determinant image are UNDETERMINED.

Field degree:

- Arithmetic 4*288*24=27648=2^10*3^3 is valid and 41 does not divide 27648.
- But [F:Q] divides 27648 is CONDITIONAL: F2 semistabilization degree 24 and
  F2/Q Galois are asserted, not proved; if F2 is not Galois its Galois closure
  may introduce other primes; F2 covers only the 2-part, while other bad primes
  19,12301,686229757 need separate semistabilization and degree control.
- Therefore the F-degree and 41-not-dividing conclusions are conditional on
  those semistabilization/Galois inputs, not arithmetic-only. The mod-41 SL2
  containment over Q is valid independently; transfer to F remains conditional.

Status: task-213 GL2 claim INVALID/superseded; SL2 containment valid. Exact H,
determinant image, F2 degree/Galois, other bad semistabilization remain open.

### E35. Task-217 Y1/Tr source obstruction for H_A-full

Task-217 / C9-Y1-TRACE-20261025.md
(SHA256 A33EBDB8D0D0551B1391CF3069C71B8CF3255D8B56F20F96513C7F33E22F425C,
179 lines) proves a source obstruction for H_A-full_H.

What the frozen Kondo data determine:

- a Q_p-basis y1,...,y_d=F(x1),...,F(x_d) of K_+, d=41;
- W=ker Tr=<y2,...,y_d>, with Tr(y1)!=0;
- y_i in J=m, so y_i vanish in I/J (E16);
- the embedding diag(1,A) of Sp_{40}(Z_p) in the y-basis;
- the mapping-class D fixes y1 in k_+;
- the structural fact Tr(y1) in pZ_p and nonzero.

What they do NOT determine:

- actual x_i in G_K or their unit parts under local reciprocity;
- actual F(x_i)=y_i in K;
- Tr(y1) beyond pZ_p nonzero;
- c=41/Tr(y1), u0=c y1, w0=1-c y1;
- the change-of-basis matrix C from the y-basis to O_K;
- explicit full-Out action matrices on O_K.

Exact formula conditional on missing data:

    1=u0+w0, u0 in U=<y1>, w0 in W, u0=c y1, c=41/Tr(y1), w0=1-c y1,
    a(alpha)=alpha_+(1)=u0+A w0 for alpha_+|U=id, alpha_+|W=A,
    H_A-full_H <=> u0+A w0 in O_K for every A in Sp_40(Z_p).          (E35.1)
The criterion is exact but undecidable from the frozen source because y1,Tr(y1),
c,C are missing.

Three admissible coordinate models satisfying the recorded axioms (not claimed
to be actual Kondo F(x_i) tuples):

- Model A: y1=p, y_i=pi^{i-1} (2<=i<=41); Tr(y1)=41p, c=1/p, u0=1, w0=0.
  Then a(alpha)=1 in O_K, H_A-full_H true, B_H=O_K.
- Model B: y1=p+pi, y2=pi,...,y41=pi^40; Tr(y1)=41p, c=1/p,
  u0=1+pi/p, w0=-pi/p. For A=-I in Sp_40(Z_p),
  a(-I)=u0-w0=1+2pi/p. Since pi/p=u*pi^{-40} has p-adic valuation -40/41,
  1+2pi/p is NOT in O_K. H_A-full_H is false; B_H is not O_K; whether B_H=I
  needs the orbit-span computation and is not decided.
- Model C: y1=2p, y_i=pi^{i-1}; Tr(y1)=82p, c=1/(2p), u0=1, w0=0.
  H_A-full_H true, B_H=O_K.
All models satisfy Q_p-basis, W=kerTr, y_i in J, J=Z_p-span(y-basis),
Sp diag(1,A), D fixes y1. A and C have different Tr/c but same H_A outcome;
A and B have same Tr/c but opposite H_A outcome.

Conclusion: the source axioms admit models with opposite H_A-full_H/B_H
outcomes; no source theorem selects one. H_A-full_H and B_H are UNDETERMINED
from the frozen source; full H_A and full B branch remain OPEN. The missing
inputs are actual x_i/y_i, Tr(y1), c, C, and explicit full-Out matrices; these
must not be chosen arbitrarily. The non-filtration of full Out (E30/E33) is
independent: even if filtration were available, y1/Tr(y1)/c/C would still be
missing.

### E36. Task-218 correction: alt E mod41 GL2 withdrawn

Task-218 / C9-MOD41-ALT-E-CORR2-20261025.md
(SHA256 D790C770F187897B45594B31FC0BF83BA09BE7BA1FCF69A380389535460AB0E9,
143 lines) corrects task-213 and supersedes its H=GL2(F41) conclusion.

- H=GL2(F41) is WITHDRAWN/INVALID. Correct:
      SL2(F41) subset H subset GL2(F41), H=Im(G_Q->GL2(F41));
  H may be SL2(F41) itself or a larger proper subgroup containing it.
  Exact H/order/determinant image remain undetermined.
- Retained exact certificate:
  Delta=-2^4*19*12301*686229757; v_p(Delta)=1; minimal; v_p(j)=-1; p=12301
  type I_1; inertia gives nontrivial unipotent of order41 in H.
  #E(F7)=10, a_7=-2; charpoly x^2+2x+7, disc 17 nonsquare (17^20=-1 mod41);
  l=7 Frobenius is irreducible in H.
- Dickson corrected: the maximal subgroups NOT containing SL2 have orders
  Borel 65600, split Cartan normalizer 3200, nonsplit Cartan normalizer 3360,
  exceptional binary polyhedral 24,48,120 (scalar preimages 480,960,2400).
  All except Borel are 41-free; order41 excludes them; irreducible excludes
  Borel. Hence SL2(F41) subset H is valid without determinant surjectivity
  or H=GL2.
- Exceptional orders corrected to 24/48/120 and 480/960/2400; task-213's
  "projective 12/24/60 times scalar center" list was imprecise.
- F=Q(zeta12,E[6],F2) degree arithmetic 4*288*24=27648=2^10*3^3 is only a
  CONDITIONAL upper bound: F2 semistabilization degree24 is asserted, not
  proved; F2 need not be Galois and its Galois closure may introduce other
  primes; F2 covers only the 2-part, while bad primes 19,12301,686229757 need
  separate semistabilization. Thus 41 not dividing [F:Q] and the transfer to F
  are conditional/missing, not unconditional. If F2 is proved Galois of
  2,3-power degree and other bad semistabilization is 2,3-smooth, the transfer
  can be repaired conditionally.

Status: task-213 H=GL2 invalid; SL2 containment valid; exact H/determinant,
F2/Galois closure/other bad semistabilization open.

### E37. Task-219 Kummer extraction fails: source obstruction stands

Task-219 / C9-F-XI-CONSTRUCT-20261025.md
(SHA256 A301BBEB1204E84ECAA2D0C6A6A94967D88A789088E56EA4471B7A4F3F09B924,
192 lines) attempts a Kummer-theoretic extraction of explicit Kondo F(x_i)/y1
and fails.

Setup/actual:

- K=Q_p(pi), e=41, p=12301, pi^41=p u, u in Z_p^times, f=1;
  p=1 mod41 so mu_41 subset Q_p and K/Q_p is cyclic tame totally ramified.
- O_K=Z_p[pi], m=(pi), J=m, I=p^{-1}J.
- Kummer theory gives the uniformizer class [pi] in K^times/(K^times)^41, a
  perfect pairing with G_K on mu_41, and a noncanonical finite-order dual basis
  after choosing generators/basis of K^times/(K^times)^41.

Failure:

- Kondo's x_i are pro-p generators of wild inertia; F(x_i) is the p-adic log of
  a pro-p unit under local reciprocity, valued in J.
- Kummer classes are finite-order (41-torsion) mod-41 data; the Kummer pairing
  is not the trace pairing x,y->Tr(xy), and local reciprocity on the pro-p part
  is not the Kummer pairing.
- The reciprocal image of a Kummer class is only defined up to G_K^41, and the
  log of its unit part depends on the pro-p lift, not just the finite-order
  class. No frozen source identifies Kondo's x_i with a chosen Kummer lift.
- Kummer data do not normalize Tr(y1), hence do not compute c=41/Tr(y1), u0,w0,
  or C. There is no source-determined y1/Tr(y1)/c/C.

Consequences:

- Determined: y-basis/W=kerTr/y_i in J/diag(1,A)/D fixes y1/Tr(y1) in pZ_p
  nonzero, and the conditional formulas
      1=u0+w0, u0=c y1, c=41/Tr(y1), w0=1-c y1,
      a(alpha)=u0+A w0, H_A-full_H iff u0+A w0 in O_K for all A in Sp_40(Z_p).
- Undetermined: y1=F(x1), Tr(y1), c, C, u0,w0, H_A-full_H, B_H.
- The task-217 models A/B/C still satisfy the recorded axioms with opposite
  H_A/B outcomes; Kummer theory does not select among them. No source-determined
  extract; this is a source obstruction, not an actual counterexample.
- Full H_A/B branch OPEN; no target/global conclusion. Missing: actual x_i/y_i,
  Tr(y1), c, C, explicit full-Out matrices, and a source theorem identifying
  Kummer classes with the pro-p JW generators.

### E38. Task-222/223 underdetermination theorem survives (with R6/corrections)

Task-222 / C9-NL-UNDERDETERMINATION-20261025.md
(SHA256 AAFE2BC84D93DEBACF06298B38D7B20694B6A04A0ADBF262DDB87D366E4D0582,
301 lines) states a natural-language underdetermination theorem; task-223 audit
C9-AUDIT-NL-UNDERDETERMINATION-20261025.md
(SHA256 BF9C2D8FF14315162DFC9FF96E520EDB7F9245797F7F891E4ECF0FEAEDBB5D99,
222 lines) verdict: the main underdetermination conclusion SURVIVES, with fixes.

Recorded data (R1)-(R5): y-basis with W=kerTr, y_i in J, U=<y1>,
Tr(y1) in pZ_p nonzero, 1=u0+w0 with u0=c y1, c=41/Tr(y1), diag(1,A) action,
a(alpha)=u0+A w0, B=closed Z_p-span of all alpha_+(O_K).

Audit result:

- Model A (y1=p, Tr=41p, c=1/p, u0=1, w0=0): VALID; H_A-full true, B=O_K.
- Model B (y1=p+pi, Tr=41p, c=1/p, u0=1+pi/p, w0=-pi/p): H_A-full FALSE is
  valid (A=-I gives a=1+2pi/p, v_p=-40/41, not in O_K); B=I is valid under the
  additional hypothesis
      (R6) H maps onto Sp_40(Z_p) in the y-basis.
  R6 is true for the actual donor H=Phi^{-1}(Sp_40(Z_p)), so the theorem is
  valid for that H; as a pure theorem about (R1)-(R5) it is incomplete.
- Identity element: id in H gives O_K subset B and the line l=O_K/J mod J, but
  does NOT force B=O_K. B=I is compatible: O_K subset I and other alpha images
  add p^{-1}L.
- u0=1+pi/p is IN I (I=p^{-1}J=pi^{-40}O_K), not outside I; v_p(u0)=-40/41,
  so u0 in I minus O_K. The task's "u0 notin I?" suspicion is false.
- a(alpha_A)=1+pi/p-A(pi/p) in I for all A; a(-I)=1+2pi/p notin O_K.
- B=I proof gap filled: identity gives O_K and 1; A=-I gives z=(a_{-I}-1)/2 in
  B; then Az=1+z-a_A in B for all A; {A pi} generates L=J cap W, so
  p^{-1}L subset B; modulo J this gives the W-part basis
  pi^{-40},...,pi^{-1}, and with l gives B/J=I/J; J subset B subset I => B=I.
- Conditional theorem H_A-full => B=O_K is VALID, and the contrapositive
  B!=O_K => H_A-full fails is VALID; no W subset J shortcut is used.
- Underdetermination conclusion survives: Models A/B satisfy (R1)-(R5) and
  (R6 for actual H), with opposite H_A-full/B outcomes. Actual F(x_i), Tr(y1),
  c, C, and full-Out integrality data are the missing source input.

Corrections to theorem statement: add R6 explicitly; state B uses all of H
including id, not just generators; include the B/J spanning argument above.
H_A underdetermination survives independently of B; B=O_K vs B=I is not
decided by the recorded structural data. No target/global conclusion.

### E39. Task-225 Lean conditional C9HAFullConditional

Task-225 / tmp/sheaf/n8/closure/C9HAFullConditional.lean
(SHA256 042581D674A9742BDC8CF0560B7037E864ABC1AE50E89CF15E532908C8167FAE,
175 lines) is an abstract Lean conditional skeleton.

Build/status recorded by the task:

- central file compiles EXIT0, sorry count 0;
- generated olean:
  .lake/build/lib/lean/tmp/sheaf/n8/closure/C9HAFullConditional.olean
  SHA256 DE05EEAABCB0596D9982164EB9E0954C1799CA9EEB1C9222052EC1431183E1C2;
- no axiom/sorry is used; this is a conditional abstract module, not a Project
  target acceptance or a closed C9/P6 result.

Formalized actual statements:

- B (G O) = additive subgroup generated by all images g(O), g in G.
- HA_full G O = every g in G maps O onto itself.
- HA_full_implies_B_eq: if the identity is in G and HA_full holds, B=O.
  Abstract Q_p-linear family only; identity membership is used explicitly.
- DecompData: one=u0+w0, u0 in U, w0 in W, U and W complementary.
- w0_eq_zero_of_one_mem_U and w0_ne_zero_of_one_not_mem_U: 1 in U iff w0=0
  (given the decomposition and U cap W=0).
- a(A)=u0+A w0; a_eq_one_of_one_mem_U; a_mem_O_of_one_mem_U;
  HA_full_a_of_one_mem_U; B_from_a_eq_O_of_one_mem_U: if 1 in U and 1 in O,
  then w0=0, a(A)=1, H_A-full holds and B=O.
- underdetermination_of_w0_ne_zero and underdetermination_of_one_not_mem_U:
  if w0!=0 (equivalently 1 notin U), two A give different a(A); abstract
  underdetermination obstruction.

Caveat/correction:

- The exact nontrivial condition formalized is w0!=0, equivalently one notin U.
  It is NOT the literal statement U != W^perp, and no trace-orthogonality
  interface is formalized in this file. Do not cite the file as proving a
  W-perp criterion or an actual Kondo F(x_i) statement.
- The file does not formalize the actual Kondo y1/Tr(y1)/c/C data, the actual
  Galois action, H_A-lite, or the full Out/B branch. It is an abstract
  Q_p-linear conditional theorem with identity and decomposition hypotheses.
- It is consistent with the E35/E38 underdetermination: Model A corresponds to
  the 1-in-U/w0=0 branch; Model B to the 1-not-in-U/w0!=0 branch. It does not
  decide which branch the source realizes.

No new attack, no target claim; target_accepted=false.

### E40. Task-226 Lean trace-orthogonal complement C9UOrthogonal

Task-226 / tmp/sheaf/n8/closure/C9UOrthogonal.lean
(SHA256 656D46D2D5E6D468AFC27D72B78A64F63580D578F4610DC85D389596E260C41D,
148 lines) is an abstract Lean formalization of the trace-orthogonal criterion.

Build/status:

- central file compiles EXIT0, sorry count 0;
- generated olean:
  .lake/build/lib/lean/tmp/sheaf/n8/closure/C9UOrthogonal.olean
  SHA256 21A710373ACC53E995AB6521F52DBE832793413C1AA11BDF207496DD7D924CA8;
- no axiom/sorry; conditional abstract module, not Project/target acceptance.

Formalized actual statements:

- TraceSetup: finite-dimensional Q_p-vector space K, nonzero trace functional
  Tr, W=ker Tr, nondegenerate reflexive bilinear form beta, beta(w,one)=0 for
  w in W, and a chosen line U with finrank U=1.
- one_mem_Wperp: one in W^perp.
- finrank_W_eq: finrank W+1=finrank K.
- finrank_Wperp_eq_one: finrank W^perp=1.
- Wperp_eq_span_one: W^perp=span{one}.
- U_eq_Wperp_iff_one_mem_U: for a line U, U=W^perp iff one in U.
- Combined with C9HAFullConditional: if one in U, one in O, and
  O=closure({one} union J), then all a(A) in O (H_A-full) and B=O.

Caveat/limits:

- The pairing beta is an abstract nondegenerate reflexive bilinear form; the
  actual field multiplication x*y and the specific trace pairing x,y->Tr(xy)
  are NOT formalized. The hypotheses beta(w,one)=0 and nondegeneracy are
  abstract interface assumptions.
- The formal U=W^perp criterion is exact for the abstract TraceSetup; it is not
  yet a formalization of the actual Kondo K/Tr/beta data, actual J/O lattice,
  H_A-lite, or full Out action.
- The conditional conclusion remains abstract: 1 in U + O=closure({1} union J)
  gives H_A-full and B=O; it does not decide whether the source realizes 1 in U.
  Together with E39 it formalizes the abstract implication, not the branch.
- No target closure, no C9/P6 acceptance; actual F(x_i)/Galois/full-Out data
  remain missing.

### E41. Task-228 normalization-independent C9 construction theorem

E47 SIGN UPDATE: F=Q_C-h_C; P6 iff F<=0. E41's Q_C-h_C<=D_C^Sp-h_inf is an
upper-bound/conservative residual, not a proof of F>0. Under the exact B=O_K
aligned b=3 profile, F=Q_p-h_A=408/41 logp and F-h_inf>=80.550578>0: a
CONDITIONAL P6 COUNTEREXAMPLE if the profile and target/TC/arch inputs are
actual. Positive RHS is not "positivity". B=I b=3 corridor: F=-S3-h_inf;
F<0 when h_inf>-S3 is P6-HOLDING, F>0 when h_inf<-S3 is counterexample. b=273
both branches F>0 are conditional counterexamples. No unconditional
counterexample/P6 proof.

Task-228 / C9-NONNORMALIZED-CONSTRUCTION-20261025.md
(SHA256 6E16AA274D78A1FBAE7F7453BAF497DA03653B2F2A098225EF70C428AB6E2348,
314 lines) proves the normalization-independent part of the C9 construction
without choosing U=<y1>, a coordinate y1, or a B=O_K/B=I branch.

Actual/normalization-independent data:

- p=12301; D=1-1728p^6=-1009*50833*1799579*64860221162029; j0=1/p^6;
  E_j: y^2=x^3-3j0/(j0-1728)x-2j0/(j0-1728), Delta=2985984p^6/D^3.
- v_p(Delta)=6, v_p(j0)=-6; E_j has type I_6 at p; Tate q has v_p(q)=6,
  q=p^6+744p^12+O(p^18)!=p^6, q/p^6 in 1+p^6Z_p.
- p does not divide 82; qhat=q^{1/82}=pi^3 v with v in 1+pZ_p; qhat^82=q,
  v_p(qhat)=3, order 3; b=3 depends only on v_p(qhat), not the unit v.
- F=Q(i,E[6],F_sem), K=F(E[41]); [F:Q] is 2,3-smooth and 41 does not divide
  [F:Q] (conditional on F_sem being the Galois semistabilization compositum):
  [Q(i):Q]=2, [Q(E[6]):Q]|288, D-part 2-power <=512, 2,3-parts only 2,3.
- Source skeleton: X_K=E_K minus origin; C_K=[X_K/E[41]] type (1,41-tors)^pm;
  C_F=[X_F/E[41]]; K-core base change; V a section over bad rational primes
  (after semistabilization only p remains); epsilon origin/canonical cusp.
  Explicit equations/stacky points/41-division/cusp coordinates missing.
- Per-D: every q|D is Kodaira III* with
  (v(c4),v(c6),v(Delta))=(3,5,9), local semistabilization degree 4;
  D-part F_sem degree 2-power <=512. Corrects task-198: 2,3 are bad additive,
  not good; exact 2,3 types/degrees missing but only 2,3 primes enter.
- Mod-41 corrected: #E(F37)=32/a37=6, #E(F127)=140/a127=-12; projective
  orders 7/5; Dickson gives SL2(F41) subset G subset GL2(F41); determinant
  classes generate only order 10; G=GL2/full determinant NOT proved.
  Conditional on [F:Q] 2,3-smooth, H=image(G_F) also contains SL2(F41) by the
  normal-index 68880/34440 contradiction; exact G/H order and determinant image
  remain open.
- Arch B_I-zero: h_inf=log r_inf (F=Q); fixed-j container pi^{j+1}B_I has
  logvolume (j+1)log pi; A_proc=((l+5)/4)log pi=11.5log pi=13.164394;
  A_proc is a procession-normalized averaged bound, not a raw pointwise
  maximal container. Shell containment r_v<=pi gives h_inf<=log pi.
- Conservative residual: with
  H_p^Sp/log p=-(1/m0)sum_j(s_j+1/e),
  d_p=b(e+1)/12-(b-1)/e-T_p,
  and under CFTH + (LB) h_p>=H_p^Sp for every bad p:
      h_C >= sum_p alpha_p H_p^Sp log p + h_inf,
      D_C^Sp=sum alpha_p d_p log p,
      Q_C-h_C <= D_C^Sp-h_inf.
  For b=3, (408/41)log12301=93.714971>A_proc; for b=273,
  (38883/41)log12301=8931.174579>A_proc, so archimedean-only compensation is
  excluded. B choice enters only in the possible B=I surplus; H_p^Sp is the
  weaker branch-independent lower bound, so no B choice is needed for (8.2).

Limits: no U/W normalization or H_A/B branch selected; no complete C;
CFTH/TC-A..H/TC-S, exact F_sem degree, explicit C equations, exact mod-41 order,
arch radius, S_bad/weights/fixed q class missing. No target closure/global
contradiction; P6 open; target_accepted=false.

### E42. Task-231 exact mod-41 G=GL2 restored via l=7 determinant

E44 UPDATE: [F:Q] is 2,3-smooth UNCONDITIONALLY (E44: divides 147456 or
294912, intersection contains Q(i)). The E42 conditional degree hypothesis is
discharged.

E46 UPDATE: task-236 verifies the transport; H=GL2(F41), order2,755,200, is
EXACT. The earlier "transport pending" qualifier is removed. E34/E36 alt-E
H=GL2 withdrawal remains unaffected.

Task-231 / C9-MOD41-EXACT-G-20261025.md
(SHA256 443A59656B1C1A7DDF3E921307FDFAE54BEAF50CDAF4542624AB3FD3A1B18ECC,
213 lines) computes the exact mod-41 image for E_j and supersedes the earlier
GL2 underclaim (task-230/205 context).

Exact classes for E_j (not the alternative E):

- #E(F7)=11, a7=-3, t7=38, d7=7 mod41;
- #E(F37)=32, a37=6, t37=6, d37=37;
- #E(F127)=140, a127=-12, t127=29, d127=4.
These are the corrected exact values; task-205's 44/116, -6/12 and
ord_41(37)=40 remain wrong.

Projective/determinant data:

- l=37: Delta=11 nonsquare, projective order 7.
- l=127: Delta=5 square, projective order 5.
- Dickson => SL2(F41) subset G=image(G_Q).
- ord_41(37)=5, ord_41(4)=10; the two classes' determinant subgroup
  <37,4> has order 10, so the subgroup they generate is
      G0=det^{-1}(<37,4>), |G0|=68,880*10=688,800, not GL2.
- l=7: determinant d7=7; ord_41(7)=40, so the determinant image is full
  F41^times. With SL2(F41) subset G, this gives
      G=GL2(F41), |G|=2,755,200, transitive over Q.
  Thus the l=7 class repairs the determinant step; task-205's numerical and
  ord_41(37)=40 reasoning remains invalid, but its GL2 conclusion is restored
  by the correct exact data.

Over F=Q(i,E[6],F_sem):

- F/Q is unramified at 41: E_j has good reduction at 41 (D mod41=-5,
  2,985,984 mod41=36 nonzero), Q(i) ramifies only at 2, and F_sem uses bad
  primes 2,3,p=12301,D-prime; 41 is not among them.
- F cap Q(zeta41)=Q, hence the cyclotomic determinant is still surjective on
  G_F; det(H)=F41^times.
- Conditional on [F:Q] 2,3-smooth, the SL2-transfer (normal H, index
  68,880/34,440 contains 5 or 7) gives SL2(F41) subset H; with full determinant,
      H=GL2(F41), |H|=2,755,200.
- Without the 2,3-smooth degree condition, det(H) is still full but H may be a
  proper determinant-full subgroup. Exact F_sem degree remains conditional.

Status: exact G=GL2 over Q; conditional H=GL2 over F. Supersedes the prior
E27/E31 underclaim for E_j (GL2 invalid based only on l=37/127). Does NOT
supersede E34/E36 alt-E H=GL2 overclaim: the alternative E has #E(F7)=10 and
is a different curve; its H=GL2 remains withdrawn. task-205's GL2 conclusion
is restored only by E42's exact data, not by its wrong counts/determinants.
Missing: exact [F:Q]/F_sem degree, explicit Frobenius matrices, full C/TC/BPS/
Theta/gluing. No target closure.

### E43. Task-233 correction 2: 2,3 local types and local p relation

E44 UPDATE: the 2,3-smoothness of [F:Q] used for H=GL2 is now unconditional.
E46 UPDATE: task-236 verifies transport and proves H=GL2(F41) exactly; the
E43 conditional H=GL2 statement is now unconditional for the degree input.
Exact [F:Q] and F0 cap F_D remain open.

Task-233 / C9-EXPLICIT-C-EQUATIONS-CORR2-20261025.md
(SHA256 C7884D5BC5B000989044C16AD174214C5837EC6DB387FAB9EC73DFEF309E5CF1,
121 lines) corrects the explicit-C file and the blanket 2,3 statement.

Corrected 2,3 local types (task-229 exact):

- p=2: minimal v_2(Delta)=0, Kodaira type I0 (good), semistabilization degree 1.
- p=3: minimal v_3(Delta)=6, Kodaira type I0* (bad additive, potential good),
  quadratic semistabilization degree 2.
- Therefore the 2,3 part of [F_sem:Q] is 2, coming only from p=3.
- This corrects both the original "2,3 minimal model good" and the task-206/E28
  blanket "2,3 bad additive": p=2 is good I0; p=3 is I0* additive degree2.
  The D-prime statement (type III*, local semistabilization degree4) is
  unchanged.
- After the quadratic F_sem extension p=3 becomes good; p=2 is already good;
  the final V_bad over F is {p=12301}; M-prime (D) potential-good additive
  contributions are 2-power and may overlap with the p=3 quadratic part; exact
  full F_sem degree remains missing.

Corrected local p relation:

- q=p^6 u with u in 1+pZ_p (indeed q/p^6 in 1+p^6Z_p); v_p(q)=6.
- v in 1+pZ_p is the unique element with v^82=q/p^6.
- pi is a uniformizer of the E[41]-local field K_v, pi^41=p, e=41, f=1.
- qhat:=pi^3 v; qhat^82=q; qhat^2=pi^6 v^2=q^{1/41}.
- qhat lies in K_v with valuation 3/41, NOT in Q_p. The earlier "q has an
  82nd root in Q_p" is wrong; the root exists only after adjoining pi.
- b=3: qhat=pi^3 v with v a unit; 41 does not divide b; v is determined by q,
  not arbitrary, and does not change b/C_v type.

Mod-41 status:

- exact over Q: G=GL2(F41), |G|=2,755,200 (task-231 exact classes at 7,37,127;
  SL2 containment plus full determinant);
- over F=Q(i,E[6],F_sem): det(H)=F41^times exactly (F/Q unramified at41,
  F cap Q(zeta41)=Q); conditional on [F:Q] 2,3-smooth,
  H=GL2(F41), |H|=2,755,200;
- exact F_sem degree still conditional.

Explicit-C skeleton:

- Retained: E_j equation/Delta/v_p=6; psi_41 recursion degree (41^2-1)/2=840,
  leading term 41x^840; E[41]=Spec F[x,y]/(E,psi_41); X_K/C_K=[X_K/E[41]] type
  (1,41-tors)^pm; C_F=[X_F/E[41]] with K-core; V section over V_mod={p};
  epsilon origin/canonical cusp.
- Missing: explicit degree-840 psi_41 polynomial/factorization, K equations and
  [K:F], Velu 41-isogeny/coarse quotient/stacky C_K equations, descent data for
  C_F, global K-places for V, explicit epsilon cusp coordinates, exact F_sem
  degree/overlap, complete C/target/P6.

### E44. Task-234 exact F_sem degree and unconditional 2,3-smooth F bound

Task-234 / C9-FSEM-DEGREE-EXACT-20261025.md
(SHA256 FFEDC1EE1912C97538AB13CB0409FC6DB4C186621BB015B084516B1DB1F46CC1,
171 lines) computes the exact semistabilization degree and field intersections.

Exact:

- D-part: for each q|D, M_q=Q(i,q^{1/4}) has degree 8; pairwise intersections
  M_q cap M_q'=Q(i). The compositum
      F_D=Q(i,q_1^{1/4},...,q_4^{1/4}), [F_D:Q]=512,
  is exact by Kummer independence over Q(i).
- p=3: I0* has quadratic semistabilization; both Q_3(sqrt3) and Q_3(sqrt-3)
  semistabilize. K3 cap F_D=Q. Hence
      [F_sem:Q]=[F_D:Q]*2=1024, exact.
- p=2 good degree1; p=12301 I6 degree1; no semistabilization fields.
- E[6] contains mu_3=Q(sqrt-3); F0=Q(i,E[6]) contains sqrt-3 and i, hence
  sqrt3=i sqrt-3; the p=3 quadratic is absorbed in F0. Therefore
      F=Q(E[6],F_D), [F:Q]=512*[F0:Q]/[F0 cap F_D:Q], [F0:Q]|576.
- F0 cap F_D contains Q(i). Hence [F:Q] divides 147456 (=512*288, using
  [F0]|576 and intersection at least 2) or 294912 (=1024*288 with F_sem
  including the absorbed p=3 quadratic). Both are 2,3-smooth; therefore
  [F:Q] is 2,3-smooth UNCONDITIONALLY. Exact [F:Q] still needs the exact
  [F0:Q] and F0 cap F_D, but the 2,3-smoothness used for the SL2 transfer no
  longer needs a conditional degree hypothesis.

Consequences:

- E42's conditional degree input "[F:Q] 2,3-smooth" is now discharged by E44.
  With E42's exact determinant full over F, H=GL2(F41), order2,755,200, follows;
  task-236/E46 verifies the transport and makes H=GL2 EXACT. Exact [F:Q]
  remains uncomputed but is not needed.
- E43's 2,3-smooth conditional statement is upgraded: the 2,3-smoothness is
  unconditional; exact [F:Q] and F0 cap F_D remain open.
- Exact [F_sem:Q]=1024; exact [F:Q] remains conditional formula, not numeric.

### E45. Task-235 psi_41 modular computation; full rational expansion missing

Task-235 / C9-PSI41-COMPUTE-20261025.md
(SHA256 92672F3AD168FC8BA7A258DB5624129FB693A0073338841B6910EE5877871A88,
151 lines) computes exact modular instances of the 41-division polynomial.

Actual/data:

- psi41 has degree (41^2-1)/2=840, leading coefficient 41, roots the 840
  x-coordinates of nonzero E[41] points (Q/-Q pairing).
- Data file psi41_mod_primes.json
  SHA256 074096F0202476DA3B3CA9A3257E4A4E827E64AFAACAA9DDA58DA6F3BD0332FD:
  exact coefficient arrays mod primes 5,7,11,13,17,19,23,29,31,37,43, degree840,
  leading/constant, discriminant mod q, resultant with cubic, root counts.
- Data file velu_quotient_mod_primes.json
  SHA256 716CAEC83C759D467BCA50FEB39083DFA378F157F2396B2563E79DC27D01F8DE:
  modular power sums p1,p2,p3, t,w, and quotient A'=a-5t, B'=b-7w mod the same
  primes.
- Verified: degree 840 and leading 41 mod every listed prime; squarefree mod
  every listed prime; resultant with the cubic nonzero; q=31 has 20 F31 roots
  of psi41, other listed primes none; exact modular recursion checks.

Limits:

- The full exact rational-coefficient expansion of psi41 was NOT completed:
  degree840, coefficients with thousands of bits, denominator powers of the
  28-digit M; order MB or more. Modular certificates verify the recursion but
  do not determine the exact rational polynomial.
- Missing: exact rational psi41 coefficients/full expansion hash, exact
  constant/trailing coefficients, exact rational t,w,A',B' and quotient
  equation, exact K=F(E[41]) field equations/[K:F]/factorization over F, explicit
  C_K/C_F stack equations, descent data, global K-places for V, cusp coordinates,
  complete C/BPS/Theta/target data.
- No arbitrary polynomial/data; modular primes are computational probes only.

### E46. Task-236 unconditional F degree bound and exact H=GL2

Task-236 / C9-MOD41-UNCONDITIONAL-20261025.md
(SHA256 4EAF8135EFF70D6D5D79B6EB66A250F58B04A1E3FF4DA6210624684A4D6F9C25,
203 lines) proves the unconditional degree bound and discharges the mod-41
degree condition.

Degree theorem:

- F0=Q(i,E[6]), [F0:Q]|576; F_sem=1024 exact (task-234).
- F=F0*F_sem; F0 cap F_sem contains Q(i), so the intersection degree is at
  least 2. Therefore
      [F:Q] = [F0][F_sem]/[F0 cap F_sem]
            <= 576*1024/2 = 294912 = 2^15*3^2.
- The bound is conservative: if the intersection contains Q(i,K3)=Q(zeta12)
  of degree4, the sharper bound is <=147456=2^14*3^2. Both are 2,3-smooth.
- Hence [F:Q] is 2,3-smooth and 41-free UNCONDITIONALLY; exact [F:Q] is not
  needed and not computed.
- F/Q is Galois because F0 and F_sem are taken as Galois closures/composites.

Mod-41 theorem:

- G=image(G_Q)=GL2(F41), |G|=2,755,200 (task-231 exact: l=37/127 give SL2,
  l=7 determinant order40 gives full determinant).
- F/Q unramified at41, F cap Q(zeta41)=Q, so det(H)=F41^times (task-231).
- [G:H] divides [F:Q] (normal H or index formula).
- If SL2(F41) were not in H, then K=H cap SL2 is 1 or {+-I} (PSL2(41) simple),
  so [G:H] is divisible by 68,880 or 34,440, hence by 5 (and 7,41). This cannot
  divide the 2,3-smooth [F:Q]. Contradiction. Therefore SL2(F41) subset H.
- With full determinant, H=GL2(F41), |H|=2,755,200 EXACT.
- This discharges E42/E43's "[F:Q] 2,3-smooth" conditional for the mod-41 image;
  E44's "transport pending" is resolved by E46. H=GL2 is now exact, not
  conditional.
- Does not affect E34/E36 alternative-E H=GL2 withdrawal (different E).

Limits: settles only the field-degree and mod-41 image part. It does not
construct complete C, resolve H_A/B, prove TC-A..TC-H/TC-S, compute the
archimedean radius, or prove P6. No U/W/B normalization used.

### E47. CRITICAL P6 sign correction: +80.55 is a conditional counterexample

E48 UPDATE: THIS E47 COUNTEREXAMPLE SECTION IS INVALID/WITHDRAWN. C1 is a
LOWER bound on h_C, so F=Q_C-h_C<=D-h_inf (an UPPER bound), not F>=D-h_inf.
The b=273 no-go and B=O_K b=3 F>=80.55 claims below are retracted; local
arithmetic, sign convention F=Q-h and C1/C3 residual survive. See E48.

Task-254 / C9-P6-SIGN-AUDIT-20261025.md
(SHA256 F4797C04CC87F6397CB15A5A4355B22DBEA179FC5895CD06AF1DE774918409A9,
241 lines) corrects the sign convention and overturns the task-245 "positivity"
reading.

Correct sign convention:

    F(C) := Q_C - h_C.
    P6 target h_C >= Q_C  <=>  F(C) <= 0.
    F>0 means Q_C>h_C, i.e. P6 FAILS for C: a counterexample.
    F<0 means h_C>Q_C: P6 holds for C.
    F=0 is the boundary.
There is no sign change in passing local to global.

Corrected classifications:

- B=O_K, b=3: F=Q_p-h_A=(408/41)log p=93.7149712746..., and with h_inf<=A,
  F-h_inf >= 93.7149712746-13.1643936873=80.5505775873>0.
  This is a CONDITIONAL P6 COUNTEREXAMPLE, not positivity and not a P6 proof.
  If the B=O_K aligned profile, finite D_3 formula, arch container, and
  target/TC inputs are actual, then h_C<Q_C and P6 is FALSE for that C.
- B=I, b=3: F=-S_3-h_inf with S_3=(12/41)log p=2.7563226845... .
  If h_inf>-S_3, F<0: P6 HOLDS in this corridor (not a counterexample).
  If h_inf<-S_3, F>0: counterexample. At h_inf=A, F=-15.920716...<0.
  Task-245 reversed this corridor.
- b=273: B=O_K F=(38883/41)log p-h_inf>0 for h_inf<=A;
  B=I F=(38463/41)log p-h_inf>0. Both are conditional counterexample
  directions, not positivity.
- Task-252's L_diff orientation deg=h_C-Q_C is correct: at b=3 B=O_K
  h_A-Q_p=-(408/41)log p, after arch <= -80.550578<0; no positive section on
  the current object. Adding a positive +80.55 term would prove a different
  inequality Q<=h+80.55, not P6.

Truth dichotomy:

(A) Conditional counterexample branch: a complete admissible C realizes the
B=O_K aligned finite formula, finite D_3, arch container bound, and
target/TC/normalization conditions. Then F>=80.55>0 and P6 is FALSE for that C.
(B) No actual realization branch: for every complete C at least one conditional
input fails (B branch not actual, finite formula not target, arch/TC/target fail,
no complete C). Then F=80.55 is only a conditional scenario, no actual
counterexample, and P6 remains open.

No third "positivity" reading exists. Positive F is failure of P6. No actual
complete C decides (A) vs (B) in the current corpus; P6 open; no genuine
unconditional counterexample constructed. The E_j/alternative-E profiles do not
supply complete C/B branch/h_inf.

Corrections to earlier ledger wording:

- Any "B=O_K b=3 residual is positivity / P6 holds" must be replaced by
  "conditional counterexample with margin 80.55".
- Any "B=I b=3 F<0 is a counterexample" must be replaced by "P6 holds in that
  corridor"; the counterexample corridor is F>0 (h_inf<-S_3).
- "b=273 F>0 is positivity" is wrong; it is a conditional counterexample.
- "No global counterexample claimed" must be qualified: no unconditional
  counterexample is constructed, but the b=3 B=O_K aligned actual profile would
  be a conditional counterexample (margin 80.55); b=273 likewise.
- E41's F<=D-h_inf is an upper-bound/conservative residual; positive RHS does
  not by itself prove F>0 unless the exact aligned profile h_C=h_A+h_inf is
  actual. The conditional counterexample reading requires that exact profile.

### E48. Task-265 logic correction: C1 gives F<=D-h_inf, not F>=

Task-265 / C9-LOGIC-CORRECTION-20261025.md
(SHA256 A0DC631787154E821DB664344BAB425D8EDEFF848DC19EB336F7E2DF6B0C21C9,
180 lines; master same correction) retracts the E47/task-254/task-256
counterexample inferences.

Error:

- C1 is a LOWER bound on h_C:
      h_C >= sum_p alpha_p H_p^Sp log p + h_inf.
- Therefore F=Q_C-h_C <= sum alpha_p(Q_p-H_p)-h_inf = D_C^Sp-h_inf:
  an UPPER bound on F. A positive upper bound does NOT prove F>0.
- Task-254/task-256/E47 used this lower bound as if it were an equality/upper
  bound and concluded F>=D-h_inf, then F>0. That is a fatal sign inversion.

Correct conditional rows:

- b=3 B=O_K: F <= 93.714971-h_inf;
- b=3 B=I: F <= -S3-h_inf; h_inf>=-S3 is SUFFICIENT for P6, not iff;
- b=273 B=O_K: F <= 8931.174579-h_inf;
- b=273 B=I: F <= 8834.703285-h_inf.
No b=3/b=273 counterexample follows from these inequalities.

Retracted/degraded:

- b=273 no-go (both branches F>=8821/8918>0) is RETRACTED; no P6 counterexample
  follows from C1/C3.
- E47 B=O_K b=3 F>=80.55 conditional counterexample is WITHDRAWN; without
  h_C=sumH+h_inf equality or a separate upper bound on h_C, no F>0 follows.
- E47 B=I corridor labels are also not established as actual; the algebra
  F<=-S3-h_inf remains, but h_inf>=-S3 is only a sufficient P6 condition, not
  an iff, and no actual h_inf equality is known.
- Task-254's "sign audit" correctly stated F=Q-h,P6<=>F<=0 but then inverted the
  C1 direction; that counterexample conclusion is withdrawn.
- Task-256 b=273 no-go is withdrawn; E2/task-260 is no longer P6-relevant.

Retained:

- Sign convention F=Q_C-h_C and P6<=>F<=0 (C98) is valid.
- C1 and C3 conditional residual inequalities are valid.
- All local b=3/b=273 arithmetic (93.714971, S3=2.7563226845, 8931.174579,
  8834.703285, A=13.164394) is valid as local arithmetic, not as a lower bound
  on F.
- Kappa-B dichotomy remains valid, but its P6 labels are corrected:
  kappa<=0=>B=OK does NOT imply b=3 P6 false; 1<=kappa<=40=>B=I gives P6 only
  if h_inf>=-S3, otherwise open; kappa>=41 not well-posed.
- Counterexample requires an upper bound h_C<=Q-eps or TC equality; P6 proof
  requires h_inf>=D_p (impossible under IV A<D). No arbitrary data.

Current P6: no proof, no conditional counterexample from C1/C3, open. History
of E47/task-254/task-256 retained but marked invalid/withdrawn.

## 3. Conditional claims that survive

C1. Corrected symplectic donor: H=Phi^{-1}(Sp_{2g}(Z_p)), mapping-class rho,
trace target Tr_{K/K^{(d=1)}}, basis alignment inferred, low-ramification J=m,
standard-lattice lemma, orbit generation T7/T8. Status: conditional source,
not paper theorem.

C2. Local source computations: T9 tensor-order formula, (10-u) per-layer
source-symplectic interior bound, p=12301 local Tate realization. Status:
conditional source/local arithmetic; not target hull.

C3. Task-148 finite hull bounds (14-u), (15-u), h_A, h_B. Status: conditional
target/branch formulas; arithmetic valid after formulas.

C4. Task-151 global assembly: W1 weights paper-level; W2/W3 templates;
G1/G3-G6/G10 conditional target assembly. Status: conditional; no G0.

C5. B=O_K vs B=I: conditional subgroup theorem and UNDETERMINED full barGamma.
Status: conditional branch, not actual.

C6. Archimedean: paper-level upper bound/radial formula, but actual r_inf and
angular terms are missing; compensation criterion is conditional. Status:
conditional/upper-bound; no actual positive compensation.

C7. Complete C weights, bad set, fixed q-volume class: assembly templates, not
constructed. Status: open.

## 4. Valid arithmetic survivor table

The following exact values survive as arithmetic for the displayed formulas.
They are not target proofs.

Uniform rho=1, e=41, m=20:

b | sum s_j | h_A | h_B | Q_p | Q_p-h_A | Q_p-h_B
--|--------:|----:|----:|---:|--------:|--------:
3 | 200 | -411/41 | 9/41 | -3/41 | 408/41 | -12/41
273 | 19100 | -39156/41 | -38736/41 | -273/41 | 38883/41 | 38463/41
1347 | 94280 | -193275/41 | -192855/41 | -1347/41 | 191928/41 | 191508/41

General rho=1/2, e=41:

b | h_{1/2} | h_direct | Q_p | Q_p-h_{1/2} | Q_p-h_direct
--|--------:|--------:|---:|------------:|-------------:
3 | -56311/10485760 | -120642551/10485760 | -3/82 | -13419889/429916160 | 4930615951/429916160
1347 | -51496081/10485760 | -172082321/10485760 | -1347/82 | -4950820039/429916160 | -6784199/429916160

Other valid arithmetic survivors:

A1. T=1/2 for b=3,273,1347; G4 identity
D_p^Sp/log p = b(e+1)/12 - (b-1)/e - T holds for these b.
A2. Uniform branch A never reaches Q_p:
h_A >= Q_p iff 41 sum s_j + 20 <= 20b, and the lower bound
41 sum s_j >= 2870b - 800 > 20b - 20 for b>=1.
A3. Branch B arithmetic: for b>=4 the B branch cannot reach Q_p; b=3 gives
9/41 local conditional value, not actual.
A4. Archimedean upper bound at l=41:
((l+5)/4) log pi = (46/4) log pi ~ 13.164394 natural;
for p>=43 this is <= 3.500052 log p; for p=12301 <= 1.397875 log p.
This is an upper bound only.
A5. Tame trace table at e=41: Tr(pi^a)=0 for 1<=a<=40, Tr(1)=41; I/J basis
(1, pi^-40,...,pi^-1); W0=ker Tr has dimension 40; field-trace line is l.
A6. Finite matrix check A=I-E_{1,21} for p=12301 is symplectic and fixes
l=(1,0,...,0); this checks a conditional matrix, not v or full barGamma.

No actual h_C, actual target hull, or Q_C <= h_C conclusion follows.

## 5. Open gaps

G1. Basis alignment and line coordinate:
- actual W-coordinate v of l=O_K/J in the 2026 symplectic basis, equivalently
  the basis-change matrix T from 2025 trace basis to 2026 symplectic basis;
- or the coordinates lambda_2,...,lambda_e of l;
- no cited source computes v/T/lambda.

G2. Full finite image:
- full barGamma on I/J beyond the subgroup H;
- condition barGamma(l)=l vs some gamma moving l;
- source-generator matrices first columns in trace-adapted basis;
- task-153 status UNDETERMINED remains correct.

G3. Target container:
- TC-A source procession/beta in Ind1;
- TC-B H_C Ind1-saturation or F target-allowed;
- TC-C integral closure/normalized volume;
- TC-D row/place;
- TC-E Theta-pilot/gluing/q-BPS/target-column;
- TC-F log/Ind3 branch;
- TC-G fixed n and arch/+infinity;
- TC-H Ism/Ind2;
- TC-S corrected symplectic donor/basis alignment/trace target/low-ramification/
  local naturality.

G4. Archimedean:
- actual r_inf/r_v from complete C;
- angular terms for non-radial hull;
- lower bound or shell containment r_v<=pi;
- no actual positive compensation; only upper bound.
- all radius figures in task-156/task-162 are stale (E8); use the corrected base
  p=12301 and C9-RADIUS-CORRECTION-20261025.md values, but the actual r_inf
  remains unconstructed.
- d_v/B_I zero-reference ambiguity (E11): task-156 mixes local d_v log(r/pi)
  with a global sum without d_v, and cites IV B_I=0 while using shell-pi as
  zero. Fix one normalization before using h_inf sign or radius; under B_I
  normalization the shell containment gives h_inf<=log pi>0, not h_inf<=0,
  and the pi factor in the radius is absent.

G5. Complete C:
- actual bad set and local types per bad p;
- row/Theta weights constructed and summed;
- fixed q-volume class identification;
- complete global construction.

G6. Range boundary:
- e>=p-1: J=m^{n0}, O_K/J is not a line; B classification and volume formulas
  do not extend; need separate treatment.

G7. Target conclusion:
- no h_C >= Q_C proof;
- no complete global counterexample;
- no F(Hull) subset H_C;
- no actual r_inf compensation.

## 6. Survivor ledger by task

task-147 (C9-SYMPLECTIC-SOURCE):
- Confirmed error correction: rho not homomorphism; H preimage; mapping-class
  source; basis alignment inferred; trace target; J=m/orbit/volume inferred.
- Survivor: corrected H donor as conditional source.
- Binding status: authoritative correction.

task-149 (C9-IND1-GLOBAL):
- Confirmed error correction: (11)-(14) not target proof; ring iso insufficient;
  full Ind1 is procession automorphism group.
- Survivor: TC-A..TC-H and TC-S as exact target conditions.
- Binding status: authoritative correction.

task-153 (C9-MODP-GENERATOR):
- Confirmed valid: full finite-image branch UNDETERMINED; exact criterion
  v=0/v!=0; e=5,p=5 finite model only.
- Survivor: source_generator_status = UNDETERMINED.
- No overclaim found.

task-155 (C9-MODP-CERTIFICATE):
- Confirmed valid: trace table, I/J basis, W0=ker Tr, conditional subgroup
  theorem for H under natural alignment; finite transvection check.
- Confirmed error: B=O_K headline as full barGamma theorem.
- Survivor: conditional subgroup theorem; B=O_K only with barGamma(l)=l.
- Current file hash E5056D...; stale report hash dad8163.

B-branch task status after task-203/E26 (E24 invalid; E26 conditional criterion):
- task-153: UNDETERMINED survives; basis-alignment matrix/T in GL_e(Z_p) not
  established; full action on I/J missing; type-gapped. No actual full action.
- task-154: trace/linear-algebra core survives; full-Gamma branch proof only
  conditional under H_A/H_A-full; E24 invalid; E26 conditional criterion only.
- task-155: trace table and conditional subgroup B=O_K survive; full-barGamma
  B=O_K invalid actual; E26 conditional H_A-full => B=O_K, B=I unavailable under
  H_A-full and not constructed outside; B=I 9/41 not selected.
- task-165: D/Aut(K) exclusion survives only as conditional k_+/alignment;
  literal I/J first-column reading type-gapped; E24 invalid; E26 conditional.
- task-180: E16/E20 type-gap audit; TAME Section 6 full-Gamma dichotomy invalid
  as written; H_A/H_A-full and actual matrices missing; E26 gives corrected
  alpha_+(1) formula and exact criterion, not H_A-full proof.
- E24/E25: INVALID per task-203 (task-196 correct, task-200 erroneous).
- E26: alpha_+(1)=p^{-1}alpha_+(p)=p^{-1}log(alpha^times(exp p)) in I is
  canonical; H_A-full(alpha) iff a(alpha) in O_K minus J; H_A-full => B=O_K and
  B=I impossible; H_A-full for full Out/Gamma_0=Out remains OPEN. Exact
  obstruction: integrality of a(alpha)/explicit alpha_+(p). Baseline: H_A-lite
  alone does not force H_A-full (abstract U(p)=pi,U(pi)=p counterexample).
  B=O_K conditional on H_A-full; B=I not selected; b=3 B=O_K 408/41 conditional,
  not actual; b=3 B=I 9/41 not selected.

Task-183 q=p^6 status after E22/E23:
- q=p^6 branch IMPOSSIBLE (E22, conditional on p-adic Mahler-Manin); rational
  j(p^6) candidate invalid.
- E23 constructs actual E_j/Q with j0=1/p^6, Delta=(2985984 p^6)/(1-1728p^6)^3,
  v_p=6, but q=p^6+744p^12+... != p^6; b=3 is actual via qhat=q^{1/82}=pi^3 v.
- O1 is partial: F=Q(i,E[6]) (degree divides 576, 41 not dividing), K=F(E[41]),
  formal X_K/C_K/V/epsilon exist; stable reduction/semistabilization, other bad
  q-orders, mod-41 SL2, explicit C_K/V/epsilon and complete C missing.
- Do not restore q=p^6; use the E23 q or another actual local q.

Task-205/task-198/task-204 status after E27-E30:
- task-205 mod-41 GL2/order 2,755,200/determinant-full claim: INVALID;
  superseded by E27 audit and E31 correction2. Valid: SL2 containment and
  conditional 2,3-smooth transfer; exact |G|/|H|/determinant missing.
- task-198 2,3-good statement: INVALID; E28 corrects to bad additive. Valid:
  D-prime III*, local semistab degree4, D-part degree 2-power <=512, F_sem
  degree 2,3-smooth 41 not dividing. Exact 2,3 types/global F_sem degree missing.
- task-204 unit-filtration integrality: INVALID; E30 cites Kondo 2025 Thm A:
  only finite Aut(k) preserves upper filtration. Full H_A-full/B=O_K/B=I for
  full Out are not proved; only Aut(k)/Gamma0 subgroup conditional. B OPEN.
- task-197 alternative E: actual b=1 profile, strict Q(zeta12) fails, larger F
  allowed; complete C missing.
- task-212 alternative E completion: source-level skeleton with F0F2/K/C/V/
  epsilon actual; p local I_1, v_p(q)=1, b=1/2, qhat=pi^{1/2} not in K_v.
  Valid alternative I_1 complete-C candidate, NOT C9 b=3. SL2 image still
  unverified; b=3 O1 remains missing.
- task-209 decisive P: P FALSE for full Out (Kondo 2025 Thm A). H infinite,
  alpha outside finite Aut(K) fails some U^n; U^e-specific preservation
  unproved; task-204 invalid. H_A-full/B=O_K/B=I full Out OPEN; canonical
  alpha_+(1) in I and criterion survive.
- task-213 mod-41 alternative E: H=GL2 overclaim INVALID; E34 audit confirms
  certificate and SL2(F41) subset H, but only SL2 subset H subset GL2; exact H
  unknown. F degree 27648 arithmetic valid; F2/F Galois/other bad semistab
  conditional. E36 correction2 (D790C770...) withdraws H=GL2 and retains
  only the SL2 certificate.
- task-217 Y1/Tr source obstruction: y1=F(x1), Tr(y1), c=41/Tr(y1), C,
  u0,w0 are NOT determined by the frozen Kondo source. Models A (y1=p,
  Tr=41p,c=1/p => H_A true/B=O_K), B (y1=p+pi, Tr=41p, A=-I => 1+2pi/p notin
  O_K => H_A false), C (y1=2p, Tr=82p,c=1/(2p) => H_A true) satisfy recorded
  axioms with opposite outcomes; no source selects. H_A-full_H/B_H
  undetermined; full H_A/B OPEN.
- task-219 Kummer extraction: FAILS/source obstruction. Kummer pairing gives
  finite-order noncanonical classes, not Kondo pro-p x_i/F(x_i); no trace
  normalization or C. y1/Tr/c/C undetermined; H_A/B OPEN.
- task-222/223 underdetermination theorem: SURVIVES. Model A valid; Model B
  H_A false valid; B=I valid under R6 (H onto Sp), true for actual donor
  H=Phi^{-1}(Sp). Identity does not force B=O_K; B=I compatible; u0=1+pi/p in I;
  B=I gap filled. H_A-full=>B=O_K valid. H_A underdetermination independent of B.
- task-225 Lean C9HAFullConditional: EXIT0/sorry0 conditional module; abstract
  HA_full=>B=O, 1-in-U=>w0=0/a=1/HA_full/B=O, underdetermination for
  w0!=0/one notin U. Caveat: exact condition w0!=0/one notin U, not
  U!=W^perp; trace orthogonality/actual Kondo data not formalized.
- task-226 Lean C9UOrthogonal: EXIT0/sorry0 abstract TraceSetup; proves
  one in W^perp, finrank W+1=finrank K, W^perp=span{one}, U=W^perp iff
  1 in U; combined with C9HAFullConditional gives 1 in U + O=closure({1}∪J)
  => H_A-full and B=O. Caveat: abstract beta, actual x*y/trace pairing not
  formalized; conditional module, not target closure.
- task-228 normalization-independent construction: actual E_j/j0/v_p/qhat b=3;
  F degree 2,3-smooth 41-free; X_K/C_K/C_F/V/epsilon skeleton; per-D III*/
  semistab4; mod41 SL2 containment; A_proc; conservative residual under
  CFTH+LB, branch-independent. No U/B choice, no target closure.
- task-231 exact mod41: E_j classes #E(F7)=11/a7=-3/det7, #E(F37)=32/a37=6/
  det37, #E(F127)=140/a127=-12/det4; two-class subgroup order688,800;
  ord_41(7)=40 => determinant full => G=GL2(F41) order2,755,200; over F
  unramified at41, F cap Q(zeta41)=Q, conditional [F:Q] 2,3-smooth =>
  H=GL2(F41) order2,755,200. Exact F_sem degree conditional; E34/E36 alt-E
  H=GL2 remains withdrawn.
- task-233/E43 correction: p=2 I0 good deg1; p=3 I0* additive deg2; 2,3 part
  F_sem degree2; local p q=p^6u, qhat=pi^3v, qhat^82=q, qhat^2=pi^6v^2; qhat
  in K_v valuation3/41 not Q_p; e41 f1 b3; mod41 G=GL2/Q exact, H=GL2/F
  conditional; explicit C skeleton with psi41 degree840/Velu/descent missing.
- task-234/E44 exact F_sem degree: [F_sem:Q]=1024, F_D=512, p3 absorbed;
  F=Q(E[6],F_D); [F] divides147456 (or294912), so [F:Q] 2,3-smooth
  unconditionally; H=GL2 exact pending task-236 transport; exact [F] still
  needs [F0] and F0 cap F_D.
- task-235/E45 psi41: modular arrays/degree840/leading41/squarefree/resultants
  and Velu modular t,w,A',B'; full rational expansion missing, so no explicit
  C_K/C_F/K equations/descent/global places.
- task-236/E46 unconditional mod41: [F:Q] <=294912=2^15*3^2 (or <=147456), hence
  2,3-smooth and 41-free unconditionally; G=GL2(Q) exact; H=GL2(F41) exact,
  |H|=2,755,200. E42/E43/E44 degree/transport conditions discharged; exact
  [F:Q] still uncomputed; E34/E36 alt-E H=GL2 remains withdrawn.
- task-254/E47 critical sign: F=Q_C-h_C; P6 iff F<=0. B=O_K b=3 F>=80.550578
  was claimed conditional counterexample; B=I b=3 F=-S3-h_inf corridor; b=273
  F>0 conditional counterexamples. E48/task-265 RETRACTS these counterexample
  claims: C1 lower bound gives F<=D-h_inf, not F>=; only sign convention,
  C1/C3 residual and local arithmetic survive. P6 open; see E48.

task-159 (C9-AUDIT-TARGET-CONTAINER):
- Confirmed valid: task-148/151 classification; valid arithmetic vs conditional
  source/target vs invalid-as-written target claims.
- No new attack claim.
- Binding status: audit reference.

task-148 (C9-UNIFORM-HULL):
- Survivors: exact arithmetic core, s_j tables, h_A/h_B values, b=3/273/1347
  and rho=1/2 values, A never closes inequality.
- Conditional: h_A/h_B as target values; B branches.
- Invalid-as-written: branch A actual; (14-u)/(15-u) actual target hull.

task-151 (C9-GLOBAL-ASSEMBLY):
- Survivors: W1 weights; G3/G4 algebra; exact local values; arch/complete-C
  gap acknowledgment.
- Conditional: G1/G6/G10 target assembly; T7/T8/T14/T15.
- Invalid-as-written: "proved" list and target containment via GLUING.

## 7. Current errata status

- C9-ERRATA-SYMPLECTIC-20261025.md is binding. It correctly states the five
  symplectic corrections.
- C9-ERRATA-IND1-20261025.md is binding in content, but its task-155 version
  pointer (dad8163...) is stale; use current E5056D....
- Any downstream file citing TAME Section 2 or Section 5 without these errata
  is invalid for target use.
- Any downstream file citing task-148/151 target bounds as actual H_C is
  invalid; use the task-159 audit classification.

## 8. Final classification

CONFIRMED ERRORS:
1. TAME Section 2 donor construction (rho image, boundary-word substitutions,
   basis alignment, trace target, J=m/orbit/volume as paper theorems).
2. TAME Section 5 (11)-(14) as target proof; ring isomorphism F to target
   inclusion.
3. task-155 B=O_K as full barGamma theorem.
4. task-148 actual/target-hull use of (14-u)/(15-u)/h_A and branch A.
5. task-151 "proved" classification of T7/T8/T14/T15 and global target use of
   G1/G6/G10.
6. C9-ARCH-GLOBAL b=273 B value -38736/41 used as h_p instead of A value
   -39156/41.
7. Archimedean radius base error E8: task-156 A18/A19 and task-162 D1/D2
   used base e=41 or omitted log p; correct base is p=12301. All prior radius
   figures 3.51816e16 / log10~1530 / pi exp(...) are withdrawn.
8. Task-146 log-domain errors E9: log converges on all U^1; n0 is the exp
   threshold; J=m^{n0} is a restricted-domain convention; volume formula drops
   f for f>1.
9. Task-150 formula/label mismatch E10: TAME (10) with -c j quoted as if it
   gave h_A=-411/41 (the h_10 value is ~-15.122); b=273 -38736/41 is B=I, not
   A=O_K -39156/41.
10. Task-156/162 archimedean normalization/radius errors E11: d_v double-count
   or omission, IV B_I=0 vs shell-pi zero reference, shell sign h_inf<=0 only
   under shell-pi, base p radius error, b=273 branch label. See E8 for the
   corrected radius numerics.
11. Task-146/161 log-domain errors E12: no log threshold; n_exp=floor(e/(p-1))+1
   and e=p-1 gives n_exp=2; J=m^{n_exp} only in the restricted convention;
   volume retains f. Task-170 supersedes task-146/161.
12. Task-173 corrected-global audit E13: residual algebra valid but conditional
   on CFTH/TC; D1/D2 radii base 41 invalid; natural alignment gives only
   B_H=O_K, not full barGamma; A_arc max-container bound conditional; b=273
   A/B labels corrected.
13. Task-174 canonical norm E15: canonical norm=(normalized norm)^d; log
   canonical=d*log normalized; d=[F_v:Q_p]=C7QPilotMassActual.d. Equality is
   false unless d=1. QPaper (canonical localSignedLog) and ThetaPaper (C6
   normalized) mix conventions; Q<=Theta is off by d without conversion. Do not
   claim equality.
14. Task-180/E16 type gap: y_i=F(x_i) in J maps to 0 in I/J; Kondo y-basis is
   not an I/J basis. Full Out is only Q_p-linear; no theorem preserves O_K/J/I or
   induces F_p action. Full-Gamma B=O_K/B=I/Q1 are invalid as written; only
   H_A/H_A-full conditional.
15. Task-179 other local types E17: restricted-shell absolute volume <=0 for
   all e (n_exp<=e); Delta_shell<=f/(p-1)logp is a normalization shift, not an
   output-hull theorem. Covering b=3 needs f>=(p-1)*408/41, b=273
   f>=(p-1)*38883/41; f unconstructed.
16. Task-181 aggregate B=I E18: N=34 is equality (34S=D3), not strict; strict
   needs N>=35 or h_inf>0; arch-adjusted 30 leaves 11.0253; D273 counts
   3241/3236; DB 3206/3201; fixed-p repeats impossible; arbitrary-prime N=1 is
   abstract; no actual C.
17. Task-182 normalization E19: binding convention is B_I-zero, h_inf=log r
   (F=Q), shell h_inf<=log pi not 0, compensation radius p^{d_p} no pi
   (b=3 5.0106595585e40; b=273 log10 3878.759836402). Shell-pi forms and
   task-156/162/166/176 shell-pi radii are stale.
18. Task-184/E20 B type-gap audit: TAME Section 6 full-Gamma dichotomy invalid
   as written; y-basis/IJ basis, U=<y1>=l, diag(1,Sp) on I/J, D-fixes-l/B=O_K,
   task-155 natural alignment=>B=O_K actual, full barGamma B=O_K/B=I/Q1, Kondo
   Theorem I as B=I, e=5,p=5 as actual are invalid. Only p=12301 trace table,
   y_i->0, x1-fixing in k_+, Q_p-linearity, Aut(K)-fixes-l are actual.
19. Task-186/E21 label errors: 40.6998948963 and 3878.759836402 are log10
   radius/log10 p^{d_p}, not log10 D; actual log10 D_3=1.9718089764...,
   log10 D_273=3.9509085787.... A_arc=11.5logpi is the final procession-
   normalized weighted-average bound, not the raw maximal container
   (j+1)logpi. B_I-zero and h_inf=log r/shell<=logpi/no-pi radius remain
   binding; D_C/radii conditional.
20. Task-191/E22 q=p^6 impossible: q=p^6 algebraic with 0<|q|_p<1;
   Mahler-Manin makes J(p^6) transcendental; j(E)=J(q_Tate) is algebraic, so
   no E/F has Tate parameter p^6 at p=12301. task-183 rational j(p^6) branch
   invalid; conditional on the cited Mahler-Manin theorem; O1 open only for an
   alternative local q.
21. Task-203 verdict: task-196 correct, task-200 erroneous, E24/task-195
   INVALID. W=ker Tr is Q_p-hyperplane not subset J; E24's W subset J step is
   false. E26 replaces it: alpha_+(1) is determined in I, H_A-full iff a(alpha)
   in O_K minus J, but H_A-full for full Out remains open. B=O_K conditional on
   H_A-full; B=I not selected; both b=3 values not actual.
22. Task-205/E27/E31 mod-41 errors: point counts 44/116 and traces -6/12 were
   sign-wrong; correct 32/6 and 140/-12. ord_41(37)=5 not 40; determinant
   subgroup order10; GL2(F41)/2,755,200/full determinant NOT proved. Correct
   SL2(F41) subset G subset GL2(F41), 68,880<=|G|<=2,755,200; transfer repaired
   via normal H/index 68,880 or 34,440 contradiction, conditional on [F:Q]
   2,3-smooth. task-205 GL2 claim superseded.
23. Task-198/E28 2,3 error: E_j is bad additive at 2,3, not good. D-primes
   are Kodaira III*, local semistabilization degree 4, D-part degree 2-power
   <=512, F_sem total degree 2,3-smooth, 41 not dividing; exact 2,3 types/global
   F_sem degree missing. E29 adds actual alternative E with b=1; strict
   Q(zeta12) fails because E[2]=S3; larger F allowed.
24. Task-204/E30 unit-filtration error: Kondo 2025 Theorem A says only the
   finite Aut(k) preserves the upper ramification filtration, not all Out.
   H=Phi^{-1}(Sp) is infinite, so some alpha in H\Aut(k) has
   alpha^times(U^n)!=U^n. a(alpha) in O_K for all Out, H_A-full full Out,
   B=O_K/B=I for full Out are INVALID; only Aut(k)/Gamma0 subgroup conditional.
   Full B branch OPEN.
25. Task-212/E32 alternative E local-type status: p local type I_1,
   v_p(q)=1, formal b=41/(2*41)=1/2 not integer; qhat=q^{1/82} has valuation
   1/82 and equals pi^{1/2}, which is not in K_v. C9 e=41/f=1/b=3/q=p^6u^6
   FAIL. The source skeleton is an actual alternative I_1 complete-C
   candidate, not a C9 b=3 complete C; O1 b=3 remains missing.
26. Task-209/E33 decisive P: full Out does NOT preserve the principal unit
   filtration U^n; Kondo 2025 Theorem A stabilizer=finite Aut(K). H infinite,
   alpha in H\Aut(K) has alpha^times(U^n)!=U^n; Theorem B second counterexample.
   Upper numbering not characteristic; U^e-specific preservation UNPROVED;
   task-204 invalid; H_A-full/B=O_K/B=I full Out OPEN. Canonical alpha_+(1) in
   I and iff a(alpha) in O_K\J survive; integrality obstruction open.
27. Task-213/E34/E36 mod-41 alternative E overclaim: H=GL2(F41) INVALID and
   WITHDRAWN. Certificate Delta/v=1/I1, #E(F7)=10/a7=-2, disc17 nonsquare,
   order41, exceptional orders 24/48/120 (preimages 480/960/2400) all valid;
   SL2(F41) subset H valid, but H may be SL2 or larger, so only SL2 subset H
   subset GL2; exact H/determinant unknown. F degree 27648 arithmetic valid;
   F2 degree24/Galois/other bad semistabilization/Galois closure conditional.
28. Task-217/E35 source obstruction: Kondo F(x_i)/trace data do not determine
   actual y1=F(x1), Tr(y1) beyond pZ_p nonzero, c=41/Tr(y1), C, u0,w0.
   Admissible models A/B/C satisfy all recorded axioms but give H_A-full_H
   true/B_H=O_K (A,C) or H_A-full_H false/B_H not O_K (B). No source selects;
   H_A-full_H/B_H UNDETERMINED; full H_A/B branch OPEN. Missing: actual
   x_i/y_i, Tr(y1), c, C, explicit full-Out matrices.
29. Task-219/E37 Kummer extraction FAILS: Kummer theory supplies only finite
   order (41-torsion) noncanonical classes; Kondo x_i are pro-p wild inertia
   generators, F(x_i)=log(unit) in J. No source identifies x_i/F(x_i) with a
   Kummer dual basis, normalizes Tr(y1), or fixes C. Hence y1/Tr(y1)/c/C remain
   undetermined; models A/B/C persist; H_A-full_H/B_H undetermined; full H_A/B
   OPEN.
30. Task-222/223 underdetermination theorem SURVIVES with fixes: Model A
   H_A true/B=O_K valid; Model B H_A false valid; B=I valid under R6
   (H onto Sp_40(Z_p), true for actual donor H=Phi^{-1}(Sp)); identity does not
   force B=O_K; u0=1+pi/p in I (v_p=-40/41); B=I gap filled via id/A=-I/
   p^{-1}L/Sp orbit. H_A-full=>B=O_K and contrapositive valid. H_A
   underdetermination survives independently of B; B=O_K vs B=I undetermined.
31. Task-225 Lean C9HAFullConditional.lean (175 lines SHA 042581D6..., olean
   DE05EEAA..., EXIT0/sorry0) is a conditional abstract module: HA_full=>B=O
   with identity in G; 1 in U=>w0=0,a=1,HA_full,B=O; underdetermination for
   w0!=0/one notin U. Caveat: exact condition is w0!=0 (one notin U), NOT
   U!=W^perp; trace orthogonality not formalized. Not Project/target acceptance;
   actual Kondo F/Galois/full-Out data absent.
32. Task-226 Lean C9UOrthogonal.lean (148 lines SHA 656D46D2..., olean
   21A71037..., EXIT0/sorry0) formalizes abstract TraceSetup: finite-dim Qp K,
   nonzero Tr, W=kerTr, nondegenerate reflexive beta with beta(w,one)=0, line U;
   proves one_mem_Wperp, finrank_W_eq, finrank_Wperp_eq_one,
   Wperp_eq_span_one, U_eq_Wperp_iff_one_mem_U. Combined with C9HAFullConditional:
   1 in U + one in O + O=closure({1} union J) => all a(A) in O and B=O.
   Caveat: beta abstract; multiplication x*y/actual trace pairing not formalized;
   conditional module, not target closure; actual Kondo data missing.
33. Task-228 normalization-independent construction: E_j/j0=1/p^6/
v_p(Delta)=6/q=p^6+744p^12/qhat=pi^3v b=3; F=Q(i,E[6],F_sem) degree
2,3-smooth 41-free; X_K/C_K/C_F/V/epsilon skeleton; per-D III*/semistab4/
D-part 2-power<=512; mod41 corrected 32/6 and 140/-12, SL2 subset G subset
GL2, conditional SL2 subset H; B_I-zero A_proc=11.5logpi; conservative residual
under CFTH+LB, branch-independent, B=O_K weaker. No U/B choice, no target
closure; CFTH/TC/complete C missing.
34. Task-231 exact mod41: exact E_j classes #E(F7)=11/a7=-3/det7,
   #E(F37)=32/a37=6/det37, #E(F127)=140/a127=-12/det4; two classes generate
   det^{-1}(<37,4>) order688,800; l=7 determinant order40 makes determinant
   full and gives G=GL2(F41), order2,755,200. Over F, F/Q unramified at41,
   F cap Q(zeta41)=Q, det full; conditional [F:Q] 2,3-smooth => H=GL2(F41),
   order2,755,200. Supersedes E27/E31 GL2 underclaim for E_j; exact F_sem
   degree conditional. E34/E36 alt-E H=GL2 withdrawal unaffected.
35. Task-233/E43 correction: p=2 I0 good degree1; p=3 I0* additive quadratic
   degree2; 2,3 part F_sem degree2 from p=3 only. Local p q=p^6u,
   v^82=q/p^6, qhat=pi^3v, qhat^82=q, qhat^2=q^{1/41}=pi^6v^2; qhat in K_v
   valuation3/41 NOT Q_p; e41 f1 b3. Mod41 exact G=GL2/Q, H=GL2 over F
   conditional on 2,3-smooth. C_K/C_F/V/epsilon skeleton; psi41 degree840/
   Velu/descent/global places missing. Supersedes E28 2,3-bad-additive blanket.
36. Task-234/E44 exact F_sem/F degree: [F_sem:Q]=1024; F_D=Q(i,q_i^{1/4}),
   [F_D:Q]=512; p=3 quadratic absorbed in F0=Q(i,E[6]); F=Q(E[6],F_D);
   [F:Q]=512[F0]/[F0 cap F_D], [F0]|576. F0 cap F_D contains Q(i) => [F]
   divides 147456 (or 294912 with F_sem), hence [F:Q] 2,3-smooth
   UNCONDITIONALLY. E42/E43 degree hypothesis discharged; H=GL2 exact pending
   task-236 transport. Exact [F:Q] remains conditional on [F0], intersection.
37. Task-235/E45 psi41 modular data: degree840, leading41, squarefree mod
   primes5..43, resultants/root counts; Velu modular t,w,A',B' data. Full exact
   rational expansion NOT completed (MB-scale/thousands bits); exact rational
   psi41/t,w/A',B', K equations/[K:F], C_K/C_F, descent, global places, cusp
   coords missing. No fully explicit C.
38. Task-236/E46 unconditional mod41: [F:Q] <= 1024*576/2 = 294912 = 2^15*3^2
   (F0 cap F_sem contains Q(i)); sharper <=147456=2^14*3^2 if Q(zeta12). Hence
   [F:Q] 2,3-smooth and 41-free UNCONDITIONALLY. G=GL2(Q) exact; [G:H] divides
   [F:Q]; PSL2(41) simple + Dickson => SL2(F41) subset H; det full over F =>
   H=GL2(F41), |H|=2,755,200 EXACT. Discharges E42/E43/E44 degree/transport
   conditions for mod41; exact [F:Q] uncomputed; E34/E36 alt-E H=GL2 withdrawn.
39. Task-254/E47 CRITICAL sign: F=Q_C-h_C; P6 h_C>=Q_C iff F<=0. Positive F
   is counterexample, not positivity. B=O_K b=3 F>=D3-A=80.550578>0 =>
   conditional P6 counterexample if exact aligned profile + finite D3 +
   target/TC/arch inputs actual (P6 false margin80.55); B=I b=3
   F=-S3-h_inf, F<0 when h_inf>-S3 is P6-holding, F>0 when h_inf<-S3 is
   counterexample; b=273 both branches F>0 conditional counterexamples. Truth
   dichotomy: (A) actual profile => P6 false; (B) conditional input fails for
   every C => P6 open. No unconditional counterexample/P6 proof.
40. Task-265/E48 RETRACTION: task-254/256/E47 used C1 LOWER bound on h_C as
   if it gave F>=; actually F=Q_C-h_C<=D-h_inf. Positive upper bound does not
   prove F>0. b=273 no-go and b=3 B=OK F>=80.55 counterexample INVALID/
   WITHDRAWN; correct rows F<=93.714971-h_inf (b3 B=OK), F<=-S3-h_inf (b3 B=I),
   F<=8931.174579-h_inf (b273 B=OK), F<=8834.703285-h_inf (B=I). Keep sign
   convention F=Q-h/P6 iff F<=0, C1/C3 residual and local arithmetic;
   counterexample needs upper bound h_C<=Q-eps/TC equality. P6 open.

CONFIRMED EXCLUSIONS / OPEN BRANCH (E14):
- mapping-class D fixes x_1/y_1 and B_D=O_K under alignment; D cannot
  realize B=I except via v!=0 (where H subset D already moves l);
- field Aut(K) fixes l and cannot realize B=I; D-conjugates fix l when v=0;
- explicit I+E_{2,1} is a finite witness but not an actual source;
- full barGamma remains UNDETERMINED; Q1 asks for an actual alpha outside
  D/Aut(K) with nonzero W first column.

CONFIRMED PARTIAL (E23):
- actual E_j/Q with j0=1/p^6, v_p(Delta)=6, q=p^6+744p^12+... != p^6;
- qhat=q^{1/82}=pi^3 v, order 3, K_v e=41/f=1;
- F=Q(i,E[6]) Galois, [F:Q]|576, 41 not dividing; K=F(E[41]);
- formal X_K/C_K/V/epsilon; source-level skeleton, not a complete C.

E26 CONDITIONAL THEOREM (after task-203 verdict):
- E24 invalid; task-196 correct; task-200 erroneous. W is the Q_p trace kernel,
  not the Z_p-span pi..pi40; W not subset J.
- alpha_+(1)=p^{-1}alpha_+(p)=p^{-1}log(alpha^times(exp p)) in I is canonical.
- H_A-full(alpha) iff a(alpha)=alpha_+(1) in O_K minus J.
- H_A-full for all actual alpha => l fixed => B_Gamma=O_K; B=I cannot occur
  while H_A-full holds.
- H_A-full for full Out/Gamma_0=Out is NOT proved; exact obstruction is the
  integrality a(alpha)/explicit alpha_+(p) or alpha^times(exp p).
- B=O_K conditional on H_A-full; B=I not available under H_A-full and not
  constructed outside; b=3 B=I 9/41 not selected; b=3 B=O_K 408/41 conditional,
  not actual. E16/E20 remain binding for the type gap/missing full action.

CONDITIONAL SURVIVORS:
- corrected H donor and mapping-class source;
- E12 corrected log theorem: log on all U^1, n_exp=floor(e/(p-1))+1, restricted
  J convention, volume with f;
- local T9/(10-u) source formulas;
- h_A/h_B branch arithmetic;
- G1/G3-G6/G10 conditional assembly and E13 residual algebra;
- E15 normalization factor d: normalized Q=canonical Q/d or canonical
  Theta=d*normalizedTheta; no equality claimed;
- B=O_K/B=I conditional branch, but type-gapped by E16/E20: only under
  H_A/H_A-full plus integral alignment; full barGamma unproved;
- E17 Delta_shell=(floor(e/(p-1))f/e)logp normalization shift, conditional and
  not an output-hull theorem; f unconstructed;
- E18 aggregate counts as conditional arithmetic (N=34 equality, not strict);
- E19 binding B_I-zero normalization: h_inf=log r (F=Q), shell bound log pi,
  radius p^{d_p}; binding formulas conditional on CFTH/TC; E21 label fixes:
  40.699.../3878... are log10 radius, not log10 D; A_arc is averaged bound,
  not raw max container;
- E20 actual survivors: p=12301 trace table, y_i->0 in I/J, x1-fixing in k_+,
  Q_p-linearity, Aut(K) fixes l;
- E22 conditional no-go: exact q=p^6 impossible for any E/F at p=12301,
  conditional on p-adic Mahler-Manin; alternative local q still open;
- E27/E31 mod-41 corrected: #E(F37)=32/a37=6, #E(F127)=140/a127=-12;
  projective orders 7/5; ord_41(37)=5, determinant order10; G=GL2 false;
  SL2(F41) subset G subset GL2(F41), 68,880<=|G|<=2,755,200; conditional
  2,3-smooth transfer via normal index 68,880/34,440 contradiction;
- E28: D-primes all Kodaira III*, local semistabilization degree4, D-part
  degree 2-power <=512; 2,3 are bad additive (not good), F_sem total degree
  2,3-smooth and 41 not dividing; only p I6/b=3 after F_sem;
- E29: actual alternative E: y^2=x^3+4x-2437249, bad {2,19,12301,686229757},
  split multiplicative at p with v_p(q)=1 (b=1), q=p(5348+1516p+...); F0
  degree 2,3-smooth 41 not dividing; strict Q(zeta12) fails (E[2]=S3);
- E30 valid: U^e=1+pO_K, exp/log, Kondo log compatibility, a(alpha)=alpha_+(1);
  only Aut(k)/Gamma0 gives H_A-full, not full Out;
- E32 actual alternative I_1 complete-C candidate: p local I_1, v_p(q)=1,
  b=1/2, qhat=pi^{1/2} not in K_v; not C9 b=3;
- E33 decisive P FALSE full Out: only finite Aut(K) preserves upper filtration;
  U^e-specific preservation unproved; H_A-full/B=O_K/B=I full Out open;
  canonical alpha_+(1) in I and criterion a(alpha) in O_K\J survive;
- E34 alternative E mod41: Delta/v=1/I1, #E(F7)=10/a7=-2, disc17 nonsquare,
  order41, exceptional orders 24/48/120 or 480/960/2400; SL2(F41) subset H
  valid, but H=GL2 invalid; only SL2 subset H subset GL2, exact H unknown;
  F degree 27648 arithmetic valid but F2/Galois/other bad semistab conditional;
- E35 Y1/Tr source obstruction: exact formula 1=u0+w0,u0=c y1,w0=1-c y1,
  c=41/Tr(y1), a(alpha)=u0+A w0; H_A-full_H iff a(alpha) in O_K. y1,Tr,c,C
  missing. Models A/B/C satisfy axioms with H_A true/B=OK (A,C) or H_A false
  (B); no source selects; H_A-full_H/B_H undetermined;
- E36 mod41 alternative E correction: H=GL2 WITHDRAWN; only
  SL2(F41) subset H subset GL2(F41), H may be SL2; certificate valid;
  exceptional 24/48/120 or 480/960/2400 41-free; F degree 27648 conditional;
- E37 Kummer obstruction: K=Qp(pi), e41, mu41 subset Qp; Kummer pairing gives
  finite-order 41-torsion/noncanonical dual basis; Kondo x_i are pro-p wild
  inertia generators, F(x_i)=log(unit) in J; no source identifies them or
  normalizes Tr(y1). y1/Tr/c/C undetermined; H_A-full_H/B_H undetermined;
- E38 underdetermination theorem: Model A H_A true/B=O_K valid; Model B H_A
  false valid; B=I valid under R6 (H onto Sp; true for actual donor
  H=Phi^{-1}(Sp)). Identity does not force B=O_K; u0=1+pi/p in I (v_p=-40/41);
  B=I gap filled via id/A=-I/p^{-1}L/Sp orbit. H_A-full=>B=O_K valid;
- E39 Lean conditional C9HAFullConditional: EXIT0/sorry0; abstract
  HA_full=>B=O with identity; 1 in U=>w0=0,a=1,HA_full,B=O; underdetermination
  for w0!=0/one notin U. Caveat: condition is w0!=0/one notin U, not
  U!=W^perp; trace orthogonality not formalized; not Project/target closure;
- E40 Lean C9UOrthogonal: EXIT0/sorry0 abstract TraceSetup; one in W^perp,
  finrank W+1=finrank K, W^perp=span{one}, U=W^perp iff 1 in U; combined with
  C9HAFullConditional gives 1 in U + O=closure({1} union J) => H_A-full and B=O;
  caveat abstract beta/actual x*y pairing not formalized; not target closure;
- E41 normalization-independent construction: actual E_j/j0/v_p/qhat b=3;
  F degree 2,3-smooth 41-free; X_K/C_K/C_F/V/epsilon skeleton; per-D III*/
  semistab4/D-part 2-power<=512; mod41 SL2 containment; A_proc=11.5logpi;
  conservative residual under CFTH+LB, branch-independent; no U/B choice;
- E42 exact mod41 GL2 restored for E_j: exact classes 7/37/127, l=7 det order40,
  G=GL2(F41) order2,755,200; over F det full and conditional [F:Q] 2,3-smooth
  => H=GL2(F41) order2,755,200; E27/E31 underclaim superseded;
- E43 corrected 2,3 local types: p=2 I0 good degree1; p=3 I0* additive degree2;
  2,3 part F_sem degree2; local p q=p^6u, qhat=pi^3v, qhat^82=q,
  qhat^2=q^{1/41}=pi^6v^2, qhat in K_v valuation3/41 not Q_p; e41 f1 b3; mod41
  G=GL2/Q exact, H=GL2/F conditional; explicit C still skeleton;
- E44 exact F_sem degree1024; F_D degree512; p3 quadratic absorbed; F=Q(E[6],F_D);
  [F] divides147456/294912 => [F:Q] 2,3-smooth unconditionally; H=GL2 exact
  pending task-236 transport; exact [F] still conditional on [F0],intersection;
- E45 psi41 modular data degree840/leading41/squarefree/resultants and Velu
  modular t,w,A',B'; full exact rational expansion missing, so no explicit C;
- E46 unconditional mod41: [F:Q] <=294912=2^15*3^2 (or <=147456), so 2,3-smooth
  and 41-free unconditionally; G=GL2(Q) exact; H=GL2(F41) exact, |H|=2,755,200;
  E42/E43/E44 degree/transport conditions discharged for mod41;
- E47 sign correction: F=Q_C-h_C; P6 iff F<=0. E48 retracts its counterexample
  claims: C1 lower bound gives F<=D-h_inf, not F>=. Correct rows F<=93.714971-
  h_inf (b3 B=OK), F<=-S3-h_inf (b3 B=I), F<=8931.174579-h_inf (b273 B=OK),
  F<=8834.703285-h_inf (B=I). Keep sign convention/C1/C3/local arithmetic; no
  conditional counterexample from these; need upper bound h_C<=Q-eps/TC eq;
- E23 actual skeleton: E_j/Q j0=1/p^6, v_p(Delta)=6, q=p^6+744p^12+...,
  qhat=q^{1/82}=pi^3 v order 3, F=Q(i,E[6]) degree|576, K=F(E[41]), formal
  C_K/V/epsilon; not a complete C;
- arch upper bound, radial formula, and A_arc conditional container bound;
- p=12301 local Tate realization.

VALID ARITHMETIC SURVIVORS:
- uniform rho=1 exact values for b=3,273,1347;
- rho=1/2 exact values for b=3,1347;
- T=1/2 and G4 identity for these b;
- uniform A never closes proof; B b>=4 inequality;
- arch upper bound numbers; tame trace table; finite transvection check.

OPEN GAPS:
- log convention (a) vs (b): full log(U^1) vs restricted m^{n_exp}; exact full
  log lattice for e>p-1 (E12);
- T/v/lambda basis alignment; E16 type gap: Kondo y-basis is Q_p, not I/J;
- H_A/H_A-full integral lift: Out action preserving O_K,J,I and inducing F_p
  action on I/J; actual full-Gamma/i>1 first columns; Q1 ill-posed without it;
- full barGamma; E14 excludes D and Aut(K) as conditional k_+ sources, but Q1
  (an actual alpha outside D/Aut(K) with nonzero I/J first column) is open;
  full barGamma branch is UNDETERMINED;
- E15 canonical vs normalized convention: d factor; no equality; choose a
  consistent Q/Theta normalization;
- E17 other local types: f, wild/e>=p-1 actual output hull, Delta_shell not
  shown to enter h_C;
- E18 aggregate counts: no actual C realizing B=I aggregate, fixed-p repeats
  impossible, arbitrary-prime N=1 abstract;
- TC-A..TC-H plus TC-S;
- actual r_inf/angular terms; E19 binding B_I-zero fixes normalization but
  A_arc remains a conditional container upper bound, not an actual radius or
  global compensation;
- complete C weights/bad set/fixed q class;
- E23 actual E_j skeleton gaps: stable reduction/semistabilization over all bad
  places, other bad q-orders and 41 non-divisibility, mod-41 image containing
  SL2(F41), explicit K equations/C_F/C_K/V/epsilon coordinates, actual complete C;
- E22 alternative local q: q=p^6 impossible; a complete C with a different
  actual q (e.g. E_j's q=p^6+744p^12+..., v_p=6/order3) is not constructed;
- E24/E26/E30: H_A-lite source proof for all Out(G_K), explicit
  a(alpha)=alpha_+(1)/alpha^times(exp p)/matrices; task-204 filtration premise
  refuted by Kondo 2025 Thm A. Full H_A-full/B=O_K/B=I open; only Aut(k)/Gamma0
  subgroup conditional; B=O_K not actual for full Out; B=I not selected;
- E33 U^e-specific preservation alpha^times(U^e)=U^e for all alpha: not proved;
  P false for full Out; H_A-full/B=O_K/B=I full Out open; only canonical
  a(alpha) in I and criterion a(alpha) in O_K\J survive;
- E34/E36 alternative E mod41 exact H and determinant image; prove H=GL2 or a
  proper larger subgroup (H=GL2 withdrawn); F2 degree24/Galois and other bad
  semistabilization/Galois closure for F degree 27648; complete C/target missing;
- E35 actual x_i/y_i, Tr(y1), c=41/Tr(y1), C, u0,w0, explicit full-Out matrices;
  without them H_A-full_H/B_H undetermined; models A/B/C show opposite outcomes
  consistent with recorded axioms;
- E37 Kummer cannot supply y1/Tr/c/C: Kummer classes are finite-order and
  noncanonical; no source identifies them with pro-p Kondo x_i/F(x_i) or
  normalizes trace. A source theorem or actual F(x_i) values are needed;
- E38 theorem as pure (R1)-(R5): add R6 (H onto Sp) and all-H span/identity
  details; actual F(x_i), Tr(y1), c, C, full-Out integrality still missing.
  H_A-full/B underdetermination survives; B=O_K vs B=I undetermined;
- E39 Lean formalization: actual Kondo F/Galois/full-Out data, H_A-lite, and
  trace-orthogonality interface not formalized; exact condition is
  w0!=0/one notin U, not U!=W^perp; conditional module not target acceptance;
- E40 Lean C9UOrthogonal: formalize actual field multiplication x*y and the
  concrete trace pairing beta(x,y)=Tr(xy), actual K/O/J/U lattice data, and
  connect TraceSetup to the actual Kondo setup; abstract beta is not enough;
- E41 remaining: actual U/B choice/H_A-full, exact 2,3 Kodaira/global F_sem
  degree, explicit C equations, exact mod41 G/H/det, actual arch radius/angular,
  CFTH/TC-A..H/TC-S, complete C/S_bad/weights, global h_C>=Q_C;
- E42 remaining: exact [F:Q]/F_sem semistabilization degree, explicit
  Frobenius matrices, full C/TC/BPS/Theta/gluing; G=GL2 exact over Q, H=GL2
  conditional over F; E34/E36 alt-E H=GL2 still withdrawn;
- E43 remaining: explicit psi41 degree840 polynomial/factorization, K equations
  and [K:F], Velu 41-isogeny/coarse quotient/stacky C_K equations, descent data,
  global K-places, epsilon cusp coordinates, exact F_sem degree/overlap; no
  fully explicit C; complete C/target/P6 missing;
- E44 remaining: exact [F0:Q], exact F0 cap F_D, hence exact [F:Q]; task-236
  transport verification for exact H=GL2; [F:Q] 2,3-smooth unconditional;
- E45 remaining: full exact rational psi41 expansion and t,w,A',B' quotient,
  K equations/[K:F], C_K/C_F stack equations, descent, global V places, cusp;
- E46 remaining: exact [F:Q] (not needed for mod41), complete C, H_A/B,
  TC-A..H/TC-S, arch radius, target/P6; H=GL2 exact only for mod41 image;
- E47 remaining (E48-corrected): no conditional counterexample from C1/C3.
  Need either h_C=sumH+h_inf equality or an upper bound h_C<=Q-eps/TC equality
  to prove P6 false; otherwise P6 open. Actual complete C/B branch/h_inf;
- E48 remaining: actual equality/upper bound for h_C, TC conditions, complete C,
  B branch; no P6 proof or counterexample from current C1/C3;
- E27/E31 mod-41 exact |G|, |H|, determinant image, explicit Frobenius matrices,
  actual [F:Q]/F_sem degree; only SL2 containment and conditional transfer known;
- E28/E29 exact 2,3 Kodaira types/global F_sem degree, semistabilization at
  2/19/686229757, explicit field equations for the alternative E; complete C
  with the b=1 profile not constructed;
- e>=p-1 boundary;
- h_C>=Q_C or global counterexample.

No new attack and no target closure. P6 remains open. target_accepted=false.

## 9. Provenance summary

Binding correction files:
- C9-SYMPLECTIC-SOURCE-20261025.md
  SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70.
- C9-IND1-GLOBAL-20261025.md
  SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8.
- C9-ERRATA-SYMPLECTIC-20261025.md
  SHA256 A189FC87D9F633916A097C2B8D9C5BDA7407825920765C1CECA36335BE5024C7.
- C9-ERRATA-IND1-20261025.md
  SHA256 EF63F916B4312A3E8562D16C2C122770BF7F188B75760989F958FDA2F6A0F8C2 (content
  binding; stale task-155 hash pointer noted).

Radius correction reference (task-167 / E8): C9-RADIUS-CORRECTION-20261025.md
SHA256 D563226D8FCDE7E01F06BCDDD5195F19530182F828C3B419997F78AB3188405D
(119 lines). All prior radius figures are stale; see E8 and W6.

Log/arch audit references (E9-E11):
- C9-AUDIT-LOG-ARCH-20261025.md
  SHA256 F7AD81083A1772BF5A300B1B05886C28831B8BBE11BAB1B097C5A817C12547EC.
- C9-AUDIT-ARCH-GLOBAL-20261025.md
  SHA256 7D719850564C1550D9D525EBE01AE395FE2AE5D70214F21AA83293EC73154825.
- Audited originals: C9-LOG-DOMAIN-EXTEND-20261025.md
  SHA256 CC52A8CF0D5FB56172A7AF2F6FB0C5C57EB726A5A459D3CCDE42FDDD3DAF2DFA;
  C9-ARCHIMEDEAN-20261025.md
  SHA256 F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957;
  C9-ARCH-GLOBAL-20261025.md
  SHA256 524E078AD85C72067627F006D165A724436E1BA508E86475C5F991860586E489;
  C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md
  SHA256 8E7EF66A737BBFE73ED13EA568875A4D1305F48D814DE4B3773BEBB3DB2F3548.

E12/E13 references:
- C9-LOG-DOMAIN-CORRECTION-20261025.md
  SHA256 882DFDEF2BF11377EBC6FDC488205623804100CC54DEEACD5EC805E75F481655.
- C9-AUDIT-GLOBAL-ASSEMBLY-20261025.md
  SHA256 916DC332D9AA15D5898062EC73C3D37E56A6CA682A9411DA0470C68647E22E6B.

E14 reference:
- C9-GAMMA-COLUMN-ATTACK-20261025.md
  SHA256 7BB5D789C5DFDA4CDDB9F39267D2AFCB961BBD369A2FD5983DAD2DC67378568C
  (140 lines).

E15 current reference:
- C9-CANONICAL-NORM-ATTACK-20261025.md
  SHA256 B13902F60B129135B33324E763880DA5C90B175A83E0E639293D3844DD48408B
  (314 lines; supersedes stale 2AD0DE86...).

E17/E18 references:
- C9-OTHER-LOCAL-TYPES-ATTACK-20261025.md
  SHA256 489708DD6D1DE159036BFADD6D6484D4470A09E31B6CD97B8F81094F3B1184DB.
- C9-AUDIT-AGGREGATE-BI-20261025.md
  SHA256 1FB1B8AB077BEB88058E9C8AF608B1D2E2C5C8E26FABBFA7F0FCE9FFCA0FD42B.

E19/E20 references:
- C9-NORMALIZATION-DECISION-20261025.md
  SHA256 5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D.
- C9-AUDIT-B-TYPEGAP-20261025.md
  SHA256 540825E769E9F2895CE2FA327719C9A5A1F46BFA751E8865CB2A16E4322BAB27.

E21 reference:
- C9-AUDIT-NORMALIZATION-DECISION-20261025.md
  SHA256 79384B32506BA7F1849BB140DC1C2CDF298748F569898417C0E8FEC3B7E10A6C
  (348 lines).

E22/E23 references:
- C9-CONSTRUCT-E-20261025.md (task-191)
  SHA256 0F4E95CD0F21921BAF93F3CC8A29BDD4BC582055B13C827D576572B74C8D422D.
- C9-CONSTRUCT-KCK-20261025.md (task-193)
  SHA256 E250D5C545AC6F152275B0FC9EC0E4966FF2917318D01B4C684143645C7FD40A.

E24 reference:
- C9-HAFULL-ALPHA1-20261025.md (task-195)
  SHA256 BA8459C4500B8E73ACFA12A3C20431C5FDF8ED1AF077DDD453F5D3C4F2E6A43B
  (145 lines).

E24/E25 conflict audits:
- task-196 C9-AUDIT-HAFULL-LITE-20261025.md
  SHA256 EF755618B74DC45913A6DD148E1E60ABC97CB6C4188748AC6F907EF9305FF223
  (correct; E24 invalid).
- task-200 C9-AUDIT-HAFULL-ALPHA1-20261025.md
  SHA256 8B63FF614DE6E3E041C850C5AB829D60EE376A7EF622176A9760F97D0A9D80A6
  (erroneous; E24 pass rejected).
- task-203 verdict recorded: task-196 correct, task-200 erroneous, E24/task-195
  invalid.

E26 reference:
- C9-HAFULL-CORRECTED-ATTACK-20261025.md (task-202)
  SHA256 A1BDFD61B7FB90D1D24EC9A3D770C308360A095F435D4A2C9F35509775356BF0
  (271 lines). Corrected canonical alpha_+(1), exact H_A-full criterion,
  conditional H_A-full=>B=O_K; H_A-full full Out remains open.

E27-E31 references:
- task-210 C9-AUDIT-MOD41-IMAGE-20261025.md
  SHA256 834873837713EEE9AFA9E056E6B5682FA6D00DFE391322B8DC3B97677F8998D3.
- task-211 C9-MOD41-IMAGE-CORR2-20261025.md
  SHA256 78FD8184AD13DC1C1DFCB2BDB90A7B92A5ECE737A6B92F83945844AEBF727140.
- task-205 C9-MOD41-IMAGE-20261025.md
  SHA256 993DE815B8442E2F44CC39877E597F7BD474180234EABE5EF4AE27DF25BBF21F
  (GL2 claim superseded).
- task-206 C9-DPRIMES-KODAIRA-20261025.md
  SHA256 DA7DFD3137E0D0287403390DAEE4039F5681648748E0366FF8D7A0A8A382AC70.
- task-197 C9-ALTERNATIVE-E-PROFILE-20261025.md
  SHA256 6E231A5D7EB23B8ACBB78E8FAEB21C6C3C8733829955628719CE1CBB8CD5A5AC.
- task-208 C9-AUDIT-UNIT-FILTRATION-20261025.md
  SHA256 8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09.
- task-204 C9-HAFULL-INTEGRALITY-20261025.md
  SHA256 16523153A35BF386899AC2F36EB6DB53C777F7CA704034615646BD84DF002929
  (conditional invalid).
- task-209 C9-PRINCIPAL-FILTRATION-P-20261025.md
  SHA256 F125420F44405B360A289CDF1787C6C4F979D122EB6E65072639DF1B6E160599
  (236 lines; P false full Out; U^e-specific preservation open).
- task-216 C9-AUDIT-MOD41-ALT-E-20261025.md
  SHA256 D8B982FD1F99C5F0147ABD3BE3333A8254E7F1F1977063DA9A0F6511F320E9CA
  (246 lines; SL2 valid, H=GL2 invalid, F-degree conditional).
- task-213 C9-MOD41-ALT-E-20261025.md
  SHA256 EB8CD3705E46AA800F99E14C974FF0EF70FB3E38F62D3CE44C22A8F044C70971
  (166 lines; GL2 claim superseded).
- task-217 C9-Y1-TRACE-20261025.md
  SHA256 A33EBDB8D0D0551B1391CF3069C71B8CF3255D8B56F20F96513C7F33E22F425C
  (179 lines; source obstruction for y1/Tr/c/C).
- task-218 C9-MOD41-ALT-E-CORR2-20261025.md
  SHA256 D790C770F187897B45594B31FC0BF83BA09BE7BA1FCF69A380389535460AB0E9
  (143 lines; H=GL2 withdrawn; SL2 only).
- task-219 C9-F-XI-CONSTRUCT-20261025.md
  SHA256 A301BBEB1204E84ECAA2D0C6A6A94967D88A789088E56EA4471B7A4F3F09B924
  (192 lines; Kummer extraction fails; source obstruction).
- task-222 C9-NL-UNDERDETERMINATION-20261025.md
  SHA256 AAFE2BC84D93DEBACF06298B38D7B20694B6A04A0ADBF262DDB87D366E4D0582
  (301 lines; underdetermination theorem).
- task-223 C9-AUDIT-NL-UNDERDETERMINATION-20261025.md
  SHA256 BF9C2D8FF14315162DFC9FF96E520EDB7F9245797F7F891E4ECF0FEAEDBB5D99
  (222 lines; theorem survives with R6/corrections).
- task-225 tmp/sheaf/n8/closure/C9HAFullConditional.lean
  SHA256 042581D674A9742BDC8CF0560B7037E864ABC1AE50E89CF15E532908C8167FAE
  (175 lines; EXIT0/sorry0; olean DE05EEAA...; conditional abstract module,
  not target acceptance).
- task-226 tmp/sheaf/n8/closure/C9UOrthogonal.lean
  SHA256 656D46D2D5E6D468AFC27D72B78A64F63580D578F4610DC85D389596E260C41D
  (148 lines; EXIT0/sorry0; olean 21A71037...; abstract TraceSetup).
- task-228 C9-NONNORMALIZED-CONSTRUCTION-20261025.md
  SHA256 6E16AA274D78A1FBAE7F7453BAF497DA03653B2F2A098225EF70C428AB6E2348
  (314 lines; normalization-independent construction theorem).
- task-231 C9-MOD41-EXACT-G-20261025.md
  SHA256 443A59656B1C1A7DDF3E921307FDFAE54BEAF50CDAF4542624AB3FD3A1B18ECC
  (213 lines; exact E_j classes, G=GL2, conditional H=GL2).
- task-233 C9-EXPLICIT-C-EQUATIONS-CORR2-20261025.md
  SHA256 C7884D5BC5B000989044C16AD174214C5837EC6DB387FAB9EC73DFEF309E5CF1
  (121 lines; 2,3 local correction, local p relation, explicit C skeleton).
- task-234 C9-FSEM-DEGREE-EXACT-20261025.md
  SHA256 FFEDC1EE1912C97538AB13CB0409FC6DB4C186621BB015B084516B1DB1F46CC1
  (171 lines; exact [F_sem:Q]=1024, unconditional 2,3-smooth F bound).
- task-235 C9-PSI41-COMPUTE-20261025.md
  SHA256 92672F3AD168FC8BA7A258DB5624129FB693A0073338841B6910EE5877871A88
  (151 lines; modular psi41/Velu data; full rational expansion missing).
  Data: psi41_mod_primes.json 074096F0..., velu_quotient_mod_primes.json
  716CAEC8....
- task-236 C9-MOD41-UNCONDITIONAL-20261025.md
  SHA256 4EAF8135EFF70D6D5D79B6EB66A250F58B04A1E3FF4DA6210624684A4D6F9C25
  (203 lines; unconditional F bound 294912/147456; exact H=GL2).
- task-254 C9-P6-SIGN-AUDIT-20261025.md
  SHA256 F4797C04CC87F6397CB15A5A4355B22DBEA179FC5895CD06AF1DE774918409A9
  (241 lines; F=Q_C-h_C sign; b=3 B=O_K F>=80.55 claim later retracted by E48).
- task-265 C9-LOGIC-CORRECTION-20261025.md
  SHA256 A0DC631787154E821DB664344BAB425D8EDEFF848DC19EB336F7E2DF6B0C21C9
  (180 lines; C1 lower bound => F<=D-h_inf; retracts E47/task-254/task-256
  counterexample claims).

Audited arithmetic/branch/target files: hashes in Section 1.

End of C9-ERROR-LEDGER-20261025.
