"""Register this root-owned natural-language package; append shared logs only."""
from pathlib import Path
import hashlib
import json

folder = Path('tmp/sheaf/n8/closure')
task = 'C9-TAME-LOG-DOMAIN-20261025'


def asset(path, **extra):
    p = Path(path)
    return dict(path=p.as_posix(), sha256=hashlib.sha256(p.read_bytes()).hexdigest(), **extra)


record = asset(folder / (task + '.md'))
sources = [
    asset('papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt',
          version='May 2020', loci=['Def3.1(a)-(e)', 'Def4.10 pp119-120']),
    asset('papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt',
          version='May 2020', loci=['Def1.1(i)', 'Rmk1.1.1(i)', 'Prop1.2(vi)',
                                    'Prop3.2', 'Prop3.4-3.5', 'Thm3.11(i)-(ii)']),
    asset('papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt',
          version='November 2015', loci=['Def5.4(iii)', 'Prop5.8(i)-(iii)']),
    asset(folder / 'sources/Kondo-2605.25428v2.html',
          version='arXiv v2, 24 September 2026', url='https://arxiv.org/html/2605.25428v2',
          loci=['section0', 'Thm1.2', 'Lem1.3/1.6', 'Thm2.6 log diagram', 'Def3.2/Lem3.3']),
    asset(folder / 'sources/Kondo-2512.09231v1.html',
          version='arXiv v1, 10 December 2025', url='https://arxiv.org/html/2512.09231v1',
          loci=['Lem1.2', 'Thm1.3', 'section2 boundary-word construction', 'Thm2.17/Rmk2.18']),
]
reused = [asset(folder / p) for p in [
    'C9-FIXED-GLUING-SWAP-20261025.md',
    'C9-FIXED-GLUING-SWAP-EVIDENCE-20261025.json',
    'C9-PROCESSION-ORBIT-20261025.md',
    'C9-FOUR-STEPS-SOURCE-ATTEMPT-20261024.md',
    'C9-EVALUATION-DEFECT-ATTACK-20261024.md',
]]
assert reused[0]['sha256'] == 'f734bc7bd33d8aa605315ad7e16709908722186ac27eece0e5a5c10cb10b1b19'
assert reused[1]['sha256'] == 'f16af247473fc1e419ea3b3c023a6643d3d057af2760282e56c38473568dc5e9'
assert sources[3]['sha256'] == 'fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86'
assert sources[4]['sha256'] == 'ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f'
artifacts = [asset(folder / 'c9_source_symplectic_span_20261025.py'),
             asset(folder / 'C9-SOURCE-SYMPLECTIC-SPAN-CERTIFICATE-20261025.json')]
cert = json.loads((folder / 'C9-SOURCE-SYMPLECTIC-SPAN-CERTIFICATE-20261025.json').read_text(encoding='utf-8'))
assert cert['all_assertions_passed'] and not cert['scope']['target_accepted']
checks = dict(root_natural_language_self_review='performed',
              exact_computations='passed, Python exit0', finite_check_counts=cert['totals'],
              statement_compiles='not_run', proof_body_checked='not_run', kernel_closed='not_run',
              project_build='not_run', comparator='not_run',
              independent_review='not_run; current root only',
              complete_global_initial_datum_constructed=False,
              original_complete_family_strict_deficit_contradiction='not_produced',
              target_accepted=False)
results = [
    'For e<p-1, log(O_K^x)=m_K; two consecutive finite-field unit-domain log links have empty domain in this type. Ambient perfection does not enlarge the allowed unit input.',
    'Kondo2026 Lem3.3 supplies actual Galois automorphisms with Sp_(e-1)(Z_p) additive image. Unit/reciprocity/perfection reconstruction matches the action with AbsTopIII5.8 and IUTIII1.2(vi).',
    'For odd tame totally ramified cyclic degree e=ell, pi^e=p*u and n=s*e+t, 1<=t<e, the full actual orbit of pi^n O_K generates p^s*m_K.',
    'The trace-zero integral lattice is a scaled standard symplectic lattice. Both pi^t and pi are primitive, so an actual source automorphism sends pi^t to pi. One genuine branch has field hull p^s*m_K, gaining (t-1)/e*log(p).',
    'A finite direct-output witness uses at most two symplectic transvections modulo p*m_K; its output is nonzero in m_K/m_K^2. Galois lifts come from the cited source theorem, not from matrix tests.',
    'With original core eta and terminal Phi fixed, actual field-copy maps on higher capsules together with eta on the 1-capsule form an allowed Psi. The actual source choice beta=Phi^-1*Psi fixes the core representative and satisfies T*beta=F in finite packet coordinates.',
    'Real branches satisfy R_(beta*gamma)=F(gamma(A(S))) in the original target. Taking the authorized hull there gives the all-bad threshold s+1/e and removes the earlier coarse tensor-order loss without commuting arbitrary additive T with hull.',
    'The full orbit-span of unmarked O_K is exactly O_K or p^-1*m_K; its actual finite action on O_K/m_K decides the branch. The larger branch has not been assumed.',
    'For the stated local bad/good profile, the integer-domain hull reaches local native q whenever rho<=1/2. For ell41/rho1/2 the actual principal-unit-domain threshold improves from b1620 to b1347, with the infinite admissible tail certified by the affine-period argument.',
    'p12301 gives a bad-local realization containing i and rational6-torsion: q=p^2694, qhat=pi^1347, pi^41=p. No complete global C is asserted.',
]
gaps = [
    'Original complete-C global P6 remains open; no local profile restriction was added to its assumptions.',
    'Uniform bad profiles, including F_mod=Q, are not covered by the successful rho<=1/2 comparison.',
    'The actual finite image moving O_K/m_K has not been computed; non-Hodge-Tate behavior alone does not choose the larger branch.',
    'No comparison of all allowed rows/Theta/log operations and actual archimedean contributions with the fixed native-q volume class has been completed.',
    'Subfamily exact values are not upper bounds on the entire source output family.',
    'The source-relative procession/Kummer/evaluation dependencies have not been implemented or independently reviewed here.',
]
next_action = (
    'Keep an original complete C with F_mod=Q as the uniform-profile test; use the new target '
    'thresholds to write the exact residual deficit, then compute actual archimedean output '
    'regions and permitted column/log-Kummer composites against that quantity. If using the '
    'larger unmarked-domain branch, compute the actual finite source action on (p^-1*m)/m; '
    'do not substitute arbitrary GL matrices.'
)
evidence = dict(
    task=task, date='2026-10-25', owner='current chat root; no subagents',
    node='n8-c9-output-region-source-route', stage='stage1 natural-language research',
    status='Actual uniformizer output and required local hull constructed source-relatively; fixed-core target realization and stronger local comparison proved; original global P6 open',
    locked_target='Every original admissible complete C, fixed native q, BPS/gluing, target column and normalization: exclude h_C<Q_C for the entire final output family',
    record=record, sources=sources, reused=reused, artifacts=artifacts,
    statement_dependencies=['Original complete C and independent native-q readout',
                            'Actual source unit domains, Gaussian action and output regions',
                            'Original processions, target hull and local/procession weights'],
    proof_dependencies=[
        dict(kind='observed_source', reference='Kondo2026 Lem3.3; Kondo2025 Thm1.3',
             purpose='actual symplectic action and trace-zero block'),
        dict(kind='observed_source', reference='AbsTopIII5.4/5.8; IUTIII1.2(vi),3.2,3.11; IUTI4.10',
             purpose='action matching and fixed-core target branches'),
        dict(kind='root_natural_language_proof', reference='record sections3-6',
             purpose='lattice orbit, actual output, target hull, finite orbit dichotomy')],
    proved_results=results,
    corrections_and_scope=[
        'Previous tensor-order calculations remain true lower bounds; full-Ind1 target alignment proves a stronger final-hull bound.',
        'Prior p1231 local example did not contain i and was never complete initial data; p12301 repairs this local requirement only.',
        'The direct uniformizer construction strengthens the orbit-span argument: a selected actual branch already has the required field hull.',
        'No tame/degree/rho/b restriction has been added to the original global target.'],
    remaining_gaps=gaps, next_action=next_action, checks=checks)
ep = folder / 'C9-TAME-LOG-DOMAIN-EVIDENCE-20261025.json'
ep.write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
eitem = asset(ep)
nodep = Path('dag/nodes/n8-c9-output-region-source-route.json')
raw = nodep.read_bytes()
node = json.loads(raw.decode('utf-8-sig'))
node['latest_tame_log_and_source_symplectic_research'] = dict(
    date='2026-10-25', owner=evidence['owner'], record=record['path'],
    record_sha256=record['sha256'], evidence=eitem['path'], evidence_sha256=eitem['sha256'],
    status=evidence['status'], proved_results=results, remaining_gaps=gaps,
    next_action=next_action, checks=checks)
assert nodep.read_bytes() == raw
nodep.write_text(json.dumps(node, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

audit = '\n\n## 2026-10-25 current chat: ' + task + '\n\n'
audit += '- Root-only natural-language stage1; no Lean/subagents; original complete-C/native-q/BPS/gluing target unchanged.\n'
audit += '- Record SHA ' + record['sha256'] + '; evidence: ' + eitem['path'] + ' (SHA ' + eitem['sha256'] + ').\n'
for result in results:
    audit += '- ' + result + '\n'
audit += '- Exact Python checks exit0:72 finite span cases,72 direct output-point cases,24 lattice and24 aligned-hull threshold sets. Root self-review only; Lean/kernel/Project/comparator/independent review not run; target_accepted=false.\n'
audit += '- Earlier frozen evidence is unchanged. Next: ' + next_action + '\n'
state = '\n\n## 2026-10-25 current chat: actual symplectic output and target hull\n\n'
state += '- ' + task + ': actual source Sp action produces a uniformizer output; field hull is p^s*m for n=s*e+t,1<=t<e. Original full-C target remains open.\n'
state += '- A complete Ind1 choice beta retains the specified core and satisfies T*beta=F on higher finite packets; actual target hull removes the prior coarse tensor-order loss.\n'
state += '- ell41/rho1/2 principal-unit-domain threshold improves to b1347; integer-domain local comparison holds for every admissible b in this profile. Uniform inputs and archimedean/global comparison remain.\n'
state += '- Evidence: ' + eitem['path'] + '. Python checks passed; no Lean/kernel/Project/comparator/independent review; target_accepted=false. Other owners unchanged.\n'
queue = '\n\n## 2026-10-25 current chat: source symplectic action reaches actual hull\n\n'
queue += '- [x] Match actual Galois Sp to source unit/reciprocity/log reconstruction; prove orbit lattice and direct uniformizer output with finite witnesses.\n'
queue += '- [x] Retain core/gluing while constructing beta with T*beta=F; deduce actual target hull and improved local comparison. Record: ' + record['path'] + '.\n'
queue += '- [x] Classify unmarked orbit as O or p^-1*m without assuming the larger branch; retain exact log domains and Gaussian integer scalar.\n'
queue += '- [ ] ' + next_action + '\n'
queue += '- [ ] Original complete-family strict-deficit contradiction/P6 remains open. No local restriction added to C; no Lean/subagents in this chat; other authorizations unchanged.\n'
for name, addition in [('AUDIT_LEDGER.md', audit), ('coord/STATE.md', state), ('coord/queue.md', queue)]:
    with Path(name).open('a', encoding='utf-8') as stream:
        stream.write(addition)
for group in [[record], sources, reused, artifacts]:
    for ent in group:
        assert asset(ent['path'])['sha256'] == ent['sha256']
assert asset(ep)['sha256'] == eitem['sha256']
assert json.loads(nodep.read_text(encoding='utf-8'))['latest_tame_log_and_source_symplectic_research']['record_sha256'] == record['sha256']
print(json.dumps(dict(record=record, evidence=eitem, verified_assets=13, checks=checks), ensure_ascii=False))
