import { readFileSync } from 'node:fs';
const d=JSON.parse(readFileSync('D:/lean/dag/declaration-dag.json','utf8'));
const N=d.nodes.map(n=>n.id); const E=d.edges.map(e=>({f:e.from,t:e.to}));
const W=1800,H=900; const P=new Map(); const cols=Math.ceil(Math.sqrt(N.length)); const sp=Math.max(18,Math.min(46,Math.sqrt((W*H)/N.length)*0.42));
N.forEach((id,i)=>{ const cx=(i%cols)-(cols-1)/2; const cy=Math.floor(i/cols)-(Math.ceil(N.length/cols)-1)/2; P.set(id,{x:W/2+cx*sp,y:H/2+cy*sp}); });
const es=E.filter(e=>P.has(e.f)&&P.has(e.t)); const MINSEP=22;
for(let it=0; it<600; it++){
 for(const e of es){ const a=P.get(e.f),b=P.get(e.t); const dx=b.x-a.x,dy=b.y-a.y; let dd=Math.hypot(dx,dy); if(dd<0.001) dd=0.001; const ux=dx/dd,uy=dy/dd; const corr=Math.max(-6,Math.min(6,dd-14))*0.5; a.x+=ux*corr;a.y+=uy*corr;b.x-=ux*corr;b.y-=uy*corr; }
 for(const e of es){ const a=P.get(e.f),b=P.get(e.t); let dy=(b.y-a.y)+14; dy=Math.max(-4,Math.min(4,dy)); b.y-=dy*0.25; a.y+=dy*0.15; }
 for(let pass=0;pass<4;pass++){ for(let i=0;i<N.length;i++){ const a=P.get(N[i]); for(let j=i+1;j<N.length;j++){ const b=P.get(N[j]); const dx=b.x-a.x,dy=b.y-a.y; const d2=dx*dx+dy*dy; if(d2>=MINSEP*MINSEP) continue; let dd=Math.sqrt(d2),ux,uy; if(dd<0.001){ ux=1;uy=0;dd=0.001; } else { ux=dx/dd;uy=dy/dd; } const push=(MINSEP-dd)*0.5; a.x-=ux*push;a.y-=uy*push;b.x+=ux*push;b.y+=uy*push; } } }
 for(const id of N){ const p=P.get(id); p.x=Math.max(30,Math.min(W-30,p.x)); p.y=Math.max(30,Math.min(H-30,p.y)); }
}
let border=0, sum=0, maxd=0; for(const id of N){ const p=P.get(id); if(p.x<=31||p.x>=W-31||p.y<=31||p.y>=H-31) border++; } for(const e of es){ const a=P.get(e.f),b=P.get(e.t); const dd=Math.hypot(b.x-a.x,b.y-a.y); sum+=dd; if(dd>maxd)maxd=dd; }
console.log(JSON.stringify({nodes:N.length,edges:es.length,border_frac:+(border/N.length).toFixed(3),mean_edge:+(sum/es.length).toFixed(2),max_edge:+maxd.toFixed(1)}));