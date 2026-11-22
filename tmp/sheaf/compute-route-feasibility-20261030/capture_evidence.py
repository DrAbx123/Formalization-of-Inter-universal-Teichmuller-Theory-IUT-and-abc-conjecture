from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re, shutil, subprocess

BASE = Path('D:/lean')
TASK = 'compute-route-feasibility-20261030'
OUT = BASE / 'tmp/sheaf' / TASK
REPORT = BASE / 'coord/reports' / (TASK + '.md')
NODE = BASE / 'dag/nodes' / (TASK + '.json')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

links = re.findall(r'\]\((D:/[^\n)]+)\)', REPORT.read_text(encoding='utf-8-sig'))
generated = {OUT / 'evidence.json', OUT / 'verification.json'}
sources = {Path(re.sub(r':\d+$', '', link)) for link in links} - generated
for rel in [
    'tmp/sheaf/compute-route-feasibility-20261030/TASK.md',
    'tmp/sheaf/compute-route-feasibility-20261030/append-record.json',
    'papers/motizuki_corpus/raw/Formalization of IUT (2026-04).pdf',
    'papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt',
    'papers/motizuki_corpus/raw/Essential Logical Structure of Inter-universal Teichmuller Theory.pdf',
    'papers/motizuki_corpus/text/Essential Logical Structure of Inter-universal Teichmuller Theory.txt',
    '.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Groebner.lean',
    '.lake/packages/mathlib/lean-toolchain',
    'tmp/sheaf/n8/closure/C9-ROUTE-CONSISTENCY-REVIEW-20261023.md',
]:
    sources.add(BASE / rel)
records = []
for path in sorted(sources):
    data = path.read_bytes()
    snapshot = OUT / 'snapshots' / path.relative_to(BASE)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(data)
    records.append({'path': path.as_posix(), 'sha256': sha(data), 'bytes': len(data),
                    'snapshot': snapshot.as_posix()})
node = json.loads(NODE.read_text(encoding='utf-8-sig'))
literature = json.loads((OUT / 'literature.json').read_text(encoding='utf-8'))
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=BASE, text=True).strip()
mathlib_head = subprocess.check_output(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], cwd=BASE, text=True).strip()
prior_checks = []
overlap_changes = []
current_map = {r['path']: r['sha256'] for r in records}
for previous_task in ['gap-exploration-20261030', 'supplement-gap-priorities-20261030']:
    prior = json.loads((BASE / 'tmp/sheaf' / previous_task / 'evidence.json').read_text(encoding='utf-8-sig'))
    previous_report = Path(prior['report']['path'])
    prior_checks.append({'task': previous_task, 'report_bytes_unchanged': sha(previous_report.read_bytes()) == prior['report']['sha256']})
    if previous_task == 'supplement-gap-priorities-20261030':
        for r in prior['source_files']:
            if r['path'] in current_map and current_map[r['path']] != r['sha256']:
                overlap_changes.append(r['path'])
manifest = {
    'schema': 'iut-exploration-evidence/v1', 'task': TASK,
    'captured_at_utc': datetime.now(timezone.utc).isoformat(),
    'head': head, 'mathlib_head': mathlib_head,
    'version_rule': 'Exact source bytes and snapshots control; a dirty workspace is not identified by HEAD alone.',
    'scope': 'Single-agent feasibility survey using primary research, targeted mathlib reads and existing failed-route evidence. No solver or proof execution.',
    'report': {'path': REPORT.as_posix(), 'sha256': sha(REPORT.read_bytes())},
    'node': {'path': NODE.as_posix(), 'sha256': sha(NODE.read_bytes())},
    'source_files': records, 'prior_reports': prior_checks,
    'overlapping_source_changes_since_priority_review': overlap_changes,
    'literature': {'path': (OUT / 'literature.json').as_posix(), 'count': len(literature['sources']), 'scope': 'See per-source read_scope; not a claim to have fully read every paper.'},
    'environment_discovery_only': {
        'python_modules': {m: importlib.util.find_spec(m) is not None for m in ['sympy', 'scipy', 'z3', 'cvxpy', 'sageall']},
        'executables': {m: shutil.which(m) for m in ['lean', 'lake', 'z3', 'sage', 'maple']},
    },
    'statement_compiles': 'not_run', 'proof_body_checked': 'not_run',
    'kernel_closed': 'not_run', 'target_accepted': False,
    'not_run': ['solver', 'proof search', 'training', 'Lean', 'Project build', 'comparator', 'axiom probe', 'independent review'],
}
dump(OUT / 'evidence.json', manifest)
dump(OUT / 'verification.json', {'status': 'checking'})
errors = []
for link in links:
    match = re.match(r'^(.*?):(\d+)$', link)
    path = Path(match.group(1) if match else link)
    if not path.is_file():
        errors.append('Missing local link: ' + link)
    elif match and not (1 <= int(match.group(2)) <= len(path.read_text(encoding='utf-8-sig').splitlines())):
        errors.append('Line outside file: ' + link)
for record in records:
    for key in ['path', 'snapshot']:
        if sha(Path(record[key]).read_bytes()) != record['sha256']:
            errors.append('Hash mismatch: ' + record[key])
for dep in node['statement_dependencies'] + node['proof_dependencies']:
    path = BASE / 'dag/nodes' / (dep + '.json')
    if not path.is_file():
        errors.append('Missing immediate dependency: ' + dep)
    else:
        d = json.loads(path.read_text(encoding='utf-8-sig'))
        if TASK in d.get('statement_dependencies', []) + d.get('proof_dependencies', []):
            errors.append('Immediate dependency backedge: ' + dep)
for record in json.loads((OUT / 'append-record.json').read_text(encoding='utf-8')):
    if sha(Path(record['path']).read_bytes()[:record['previous_bytes']]) != record['previous_sha256']:
        errors.append('Historical document prefix changed: ' + record['path'])
if not all(c['report_bytes_unchanged'] for c in prior_checks):
    errors.append('A historical report changed from its manifest')
if overlap_changes:
    errors.append('Shared source changed since priority review: re-read before concluding')
if head != literature['local_version']['workspace_head'] or mathlib_head != literature['local_version']['mathlib_head']:
    errors.append('Recorded HEAD differs from actual HEAD')
for f in [NODE, OUT / 'evidence.json', OUT / 'literature.json', OUT / 'local-searches.json']:
    json.loads(f.read_text(encoding='utf-8-sig'))
verification = {
    'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'pass': not errors,
    'local_links_checked': len(links), 'source_snapshots_checked': len(records),
    'errors': errors, 'prior_reports': prior_checks,
    'dag_scope': 'New node and immediate dependencies only',
    'network_links': 'Cited from this survey; no claim of a second end-of-task URL availability test',
    'mathematical_and_Lean_verification': 'not_run', 'solver_execution': 'not_run',
    'target_accepted': False,
}
dump(OUT / 'verification.json', verification)
print(json.dumps(verification, ensure_ascii=False))
if errors:
    raise SystemExit(1)
