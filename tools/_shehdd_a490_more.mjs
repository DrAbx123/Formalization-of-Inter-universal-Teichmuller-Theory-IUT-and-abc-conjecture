import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/sheaf/lana/iut/Iut';
const files=['WallEquiv/Forms.lean','WallEquiv/VcI.lean','Wall/Constraints.lean','Wall/Pilots.lean','Wall/Scaling.lean','Wall/MultiContainer.lean'];
const pats=[/def SSIneq/,/theorem ss_iff_lgp_vcI/,/def Wall/,/def IPL/,/def SHE/,/def APT/,/pilot_qVal_eq_neg_lhs/,/lhs_neg/,/two_le_ellStar/,/wallS/,/absLogQ_pos/,/shift_qScale/,/logVol_act/,/isAdelic_act /,/def qScale/,/def Multiradial/];
for(const p of pats){
  let done=false;
  for(const rel of files){ if(done) break; const f=base+'/'+rel; if(!existsSync(f)) continue; const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(p.test(t[i])){ console.log(rel+':'+(i+1)+': '+t[i].trim().slice(0,180)); done=true; break; } } }
}
