from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess

BASE = Path('D:/lean')
TASK = 'source-compute-integration-20261030'
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
    'tmp/sheaf/source-compute-integration-20261030/TASK.md',
    'tmp/sheaf/source-compute-integration-20261030/append-record.json',
    'papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt',
    'papers/motizuki_corpus/text/Essential Logical Structure of Inter-universal Teichmuller Theory.txt',
    'tmp/sheaf/xif/paper/IPLAPTActual.lean',
    'tmp/sheaf/xif/paper/GlobalThetaPilotPossibleImagesActual.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean',
    'LeanFormal/IUT/IUTIII/Theorem311/SourceMultiradialTwoActionEquivalence.lean',
]:
    sources.add(BASE / rel)
records = []
for path in sorted(sources):
    data = path.read_bytes()
    snapshot = OUT / 'snapshots' / path.relative_to(BASE)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(data)
    records.append({'path': path.as_posix(), 'sha256': sha(data), 'bytes': len(data), 'snapshot': snapshot.as_posix()})
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=BASE, text=True).strip()
node = json.loads(NODE.read_text(encoding='utf-8-sig'))
prior_checks = []
overlap_changes = []
current_map = {r['path']: r['sha256'] for r in records}
for task in ['gap-exploration-20261030', 'supplement-gap-priorities-20261030', 'compute-route-feasibility-20261030']:
    prior = json.loads((BASE / 'tmp/sheaf' / task / 'evidence.json').read_text(encoding='utf-8-sig'))
    prior_checks.append({'task': task, 'report_unchanged': sha(Path(prior['report']['path']).read_bytes()) == prior['report']['sha256']})
    if task == 'compute-route-feasibility-20261030':
        for r in prior['source_files']:
            if r['path'] in current_map and current_map[r['path']] != r['sha256']:
                overlap_changes.append(r['path'])
manifest = {
    'schema': 'iut-exploration-evidence/v1', 'task': TASK,
    'captured_at_utc': datetime.now(timezone.utc).isoformat(), 'head': head,
    'version_rule': 'Actual source hashes identify the read dirty-workspace versions; no Lean build performed.',
    'scope': 'Single-agent concrete design; proposed modules/types/signatures are not implementations.',
    'report': {'path': REPORT.as_posix(), 'sha256': sha(REPORT.read_bytes())},
    'node': {'path': NODE.as_posix(), 'sha256': sha(NODE.read_bytes())},
    'source_files': records, 'prior_reports': prior_checks,
    'overlapping_source_changes_since_feasibility_review': overlap_changes,
    'search_limits': 'Targeted declarations and consumers only. Guessed missing paths were not used as evidence of mathematical absence.',
    'statement_compiles': 'not_run', 'proof_body_checked': 'not_run',
    'kernel_closed': 'not_run', 'target_accepted': False,
    'not_run': ['solver', 'Lean', 'Project build', 'comparator', 'axiom probe', 'independent review'],
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
for r in json.loads((OUT / 'append-record.json').read_text(encoding='utf-8')):
    if sha(Path(r['path']).read_bytes()[:r['previous_bytes']]) != r['previous_sha256']:
        errors.append('Historical prefix changed: ' + r['path'])
if not all(r['report_unchanged'] for r in prior_checks):
    errors.append('Historical report changed')
if overlap_changes:
    errors.append('Shared source changed: re-read before concluding')
verification = {
    'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'pass': not errors,
    'local_links_checked': len(links), 'source_snapshots_checked': len(records),
    'errors': errors, 'prior_reports': prior_checks,
    'dag_scope': 'New node and immediate dependencies only',
    'proposed_Lean_modules': 'not_created', 'mathematical_and_Lean_verification': 'not_run',
    'target_accepted': False,
}
dump(OUT / 'verification.json', verification)
print(json.dumps(verification, ensure_ascii=False))
if errors:
    raise SystemExit(1)
