import csv,math,statistics as st
rows=list(csv.DictReader(open('coord/b1_exact_snf_1000.csv')))
out=[]
for lo in range(0,1000,100):
 a=[r for r in rows if lo<=int(r['N'])<lo+100]
 z=[r for r in a if int(r['min_abs'])>0]
 cs=[math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in z]
 out.append(dict(N_lo=lo,N_hi=lo+100,rows=len(a),zero=sum(1 for r in a if int(r['min_abs'])==0),positive=len(z),max_abs=max([int(r['min_abs']) for r in a] or [0]),max_Cobs=max(cs) if cs else '',median_Cobs=st.median(cs) if cs else '',mean_Cobs=st.mean(cs) if cs else ''))
with open('coord/b1_exact_snf_bins.csv','w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(out[0].keys())); w.writeheader(); w.writerows(out)
print('wrote bins')
