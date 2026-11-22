import csv,math,statistics as st
files={'n500_p60':'coord/b1_exact2_500_p60.csv','n500_p200':'coord/b1_exact2_500_p200.csv','n1000_p60':'coord/b1_exact2_1000_p60.csv','n1000_p200':'coord/b1_exact2_1000_p200.csv'}
summary=[]
for name,fn in files.items():
    rows=list(csv.DictReader(open(fn)))
    pos=[r for r in rows if int(r['min_abs'])>0]
    cs=[math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in pos]
    z=[(math.log(int(r['N'])),math.log(int(r['min_abs']))) for r in pos]
    xs=[a for a,b in z]; ys=[b for a,b in z]; mx=st.mean(xs); my=st.mean(ys)
    slope=sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs) if z else 0
    vd=sum(1 for r in pos if r['valid_div']=='True'); vg=sum(1 for r in pos if r['valid_ge']=='True')
    print('==',name,'rows',len(rows),'pos',len(pos),'zero',len(rows)-len(pos),'valid_div',vd,'/',len(pos),'valid_ge',vg,'/',len(pos),'Cmax',max(cs) if cs else None,'Cmed',st.median(cs) if cs else None,'Cmean',st.mean(cs) if cs else None,'slope',slope)
    bins=[]
    for lo in range(0,1000,100):
        a=[r for r in rows if lo<=int(r['N'])<lo+100]; zz=[r for r in a if int(r['min_abs'])>0]
        cc=[math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in zz]
        b={'lo':lo,'rows':len(a),'zero':len(a)-len(zz),'pos':len(zz),'max':max(cc) if cc else '', 'med':st.median(cc) if cc else '', 'mean':st.mean(cc) if cc else ''}
        bins.append(b)
        if a: print('  BIN',lo,len(a),'zero',b['zero'],'pos',b['pos'],'max',b['max'],'med',b['med'],'mean',b['mean'])
    summary.append({'name':name,'rows':len(rows),'pos':len(pos),'zero':len(rows)-len(pos),'valid_div':vd,'valid_ge':vg,'Cmax':max(cs) if cs else '','Cmed':st.median(cs) if cs else '','Cmean':st.mean(cs) if cs else '','slope':slope})
with open('coord/b1_exact2_bins.csv','w',newline='') as f:
    w=csv.writer(f); w.writerow(['dataset','N_lo','N_hi','rows','zero','positive','Cmax','Cmedian','Cmean'])
    for name,fn in files.items():
        rows=list(csv.DictReader(open(fn)))
        for lo in range(0,1000,100):
            a=[r for r in rows if lo<=int(r['N'])<lo+100]; zz=[r for r in a if int(r['min_abs'])>0]
            cc=[math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in zz]
            w.writerow([name,lo,lo+100,len(a),len(a)-len(zz),len(zz),max(cc) if cc else '',st.median(cc) if cc else '',st.mean(cc) if cc else ''])
with open('coord/b1_exact2_summary.csv','w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(summary[0].keys())); w.writeheader(); w.writerows(summary)
print('wrote summary/bins')
