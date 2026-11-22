import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
for(const e of d.edges){
  if((e.from==='iutiii:IUTIII.IUTII_LINK_GAP'&&e.to==='iutiii:IUTIII.STEPXI.CONTRACT')||(e.from==='iutiii:IUTIII.STEPXI.CONTRACT'&&e.to==='iutiii:IUTIII.IUTII_LINK_GAP')) console.log('MERGED: '+e.from+' -> '+e.to+' ['+e.kind+']');
}
for(const f of readdirSync(ROOT+'/coord')){ if(!/^target-chain\..+\.json$/.test(f)||f==='target-chain.TEMPLATE.json') continue; let j; try{ j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8')); }catch{ continue; } for(const e of (j.edges||[])){ if(e.from.includes('IUTII_LINK_GAP')||e.to.includes('IUTII_LINK_GAP')||e.from.includes('STEPXI.CONTRACT')||e.to.includes('STEPXI.CONTRACT')) console.log(f+' :: '+e.from+' -> '+e.to+' ['+e.kind+']'); } }
