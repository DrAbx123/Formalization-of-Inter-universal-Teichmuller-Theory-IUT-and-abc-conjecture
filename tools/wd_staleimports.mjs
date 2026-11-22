import { readFileSync, existsSync, statSync } from "node:fs";
const ROOT="D:/lean";
const norm=p=>p.trim().replaceAll("\\","/").replace(/^D:\/lean\//i,"").replace(/^\.\//,"");
const modToFile=(m)=>{
  if(m.startsWith("tmp.sheaf.xif.paper.")) return "tmp/sheaf/xif/paper/"+m.slice("tmp.sheaf.xif.paper.".length).replaceAll(".","/")+".lean";
  if(m.startsWith("tmp.sheaf.")) return "tmp/sheaf/"+m.slice("tmp.sheaf.".length).replaceAll(".","/")+".lean";
  if(m.startsWith("tmp.external.ported.")) return "tmp/external/ported/"+m.slice("tmp.external.ported.".length).replaceAll(".","/")+".lean";
  if(m.startsWith("LeanFormal.")) return "LeanFormal/"+m.slice("LeanFormal.".length).replaceAll(".","/")+".lean";
  if(m.startsWith("Mathlib.")) return ".lake/packages/mathlib/Mathlib/"+m.slice("Mathlib.".length).replaceAll(".","/")+".lean";
  if(m.startsWith("Iut.")) return "Iut/"+m.slice("Iut.".length).replaceAll(".","/")+".lean";
  return null;
};
const oleanFor=(file)=>{
  if(file.startsWith("tmp/external/ported/")){ const rest=file.slice("tmp/external/ported/".length); const pkg=rest.split("/")[0]; const rel=rest.split("/").slice(1).join("/"); return "tmp/external/ported/"+pkg+"/.lake/build/lib/lean/"+rel.replace(/\.lean$/,"")+".olean"; }
  if(file.startsWith(".lake/packages/mathlib/")) return ".lake/packages/mathlib/.lake/build/lib/lean/"+file.slice(".lake/packages/mathlib/".length).replace(/\.lean$/,"")+".olean";
  return ".lake/build/lib/lean/"+file.replace(/\.lean$/,"")+".olean";
};
const targets=process.argv.slice(2).map(norm);
for(const p of targets){
  const abs=ROOT+"/"+p;
  let imports=[];
  try{ imports=readFileSync(abs,"utf8").split(/\r?\n/).map(l=>l.match(/^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$/)).filter(Boolean).map(m=>m[1]); }catch{ console.log(p+"\tNO-SRC"); continue; }
  const stale=[];
  for(const m of imports){
    const f=modToFile(m); if(!f) continue;
    const fa=ROOT+"/"+f, oa=ROOT+"/"+oleanFor(f);
    if(!existsSync(fa)) continue;
    try{ const s=statSync(fa); if(existsSync(oa)){ const o=statSync(oa); if(s.mtimeMs>o.mtimeMs) stale.push(m);} else if(!m.startsWith("Mathlib.")) stale.push(m+"(no-olean)"); }catch{}
  }
  console.log(p+"\t"+(stale.length?("STALE-IMPORTS: "+stale.join(", ")):"imports-fresh"));
}
