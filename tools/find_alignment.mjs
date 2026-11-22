import { readFileSync } from 'node:fs';
const idx=JSON.parse(readFileSync('D:/lean/dag/generated/declarations-index.json','utf8')).declarations;
const terms=['alignment','Alignment','socket','Socket','hq_align','hth','SourceColumnCarrierIdentification'];
for(const t of terms){ const hits=idx.filter(d=>d.name.includes(t)); console.log('##',t,'hits',hits.length); for(const h of hits.slice(0,15)) console.log(' ',h.kind,h.name,'@',h.file); }