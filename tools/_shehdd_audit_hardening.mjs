import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/PROBE-AUDIT.md';
let txt=readFileSync(p,'utf8');
const ap=readdirSync(ROOT+'/tmp/sheaf/xif/paper').filter(f=>f.startsWith('_AutoProbe_')).length;
const add='\n## Appendix: generator hardening ('+new Date().toISOString()+')\n\n- Multi-namespace FQN: scope-stack parser (namespace vs section separated).\n- Comment stripping: block comments and line comments are removed before declaration scan, so docstring pseudo-declarations (for example a doc line starting with the word theorem) no longer produce invalid #print axioms targets.\n- Declaration regex now accepts names ending at end-of-line.\n- '+ap+' AutoProbe files; 37 probes content-updated by comment-stripping pass; no deletions.\n';
if(!txt.includes('## Appendix: generator hardening')) txt+=add;
writeFileSync(p,txt);
console.log('audit hardening note appended, probes='+ap);
