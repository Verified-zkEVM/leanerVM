import os, sys
# usage: python3 -I genair.py  writes Tables/Vt/Air.lean (each table's weight and form value; the final claim).
# First run: python3 -I dump.py ../../LeanVM/Guest/Data/Core00.lean vt_ir.txt (from this directory).
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genforms import *
from mk import write
CE=[6382,6887,7150,7650,8121,11189]
TAU=[5938,6390,6896,7159,7659,8130]
# air_t = mul(mul(cp,pe), CE)
out=[]
def at(p): return f'  have a{p} := h.atom {p} {RAW[p][len(".atom "):]} (by decide +kernel)'
airs=[]
for t in range(6):
    # find air var: mul X CE
    air=[v for v,(p,op,a) in D.items() if op=='mul' and a[1]==CE[t]][0]
    airs.append(air)
    pa,_,(w,_)=D[air]
    pw,_,(cp,pe)=D[w]
    pcp,_,(cpb,_)=D[cp]   # load cp from cpb 0
    pcpb,_,(s5915,x)=D[cpb]
    ppe,_,(peb,_)=D[pe]
    ppeb,_,(s5936,tau)=D[peb]
    assert tau==TAU[t] and s5915==5915 and s5936==5936
    # 5817 = x * tau atom
    pm=[q for q in range(pcp-6,pcp) if RAW[q]==f'.atom (.mul (.n 5817) (.n {x}) (.n {tau}))'][0]
    ptau=[q for q in range(5200,10251) if RAW[q]==f'.atom (.load (.n {tau}) (.n 10) {t+1})'][0]
    pce,_,_=D[CE[t]]
    # CE expr
    ceat=set(); deps_stop(CE[t],D,ceat,set(FV[str(t)][sd] for sd in range(3))|set(evvar))
    stop=set(FV[str(t)][sd] for sd in range(3))|set(evvar)
    def ex(v):
        if v in evvar: return f'ev {evvar[v]-BASE[t]}'
        if v in stop or v not in D or D[v][0] not in ceat: return f'σ (.n {v})'
        p,op,a=D[v]
        if op=='const': return f'word {a[0]} {a[1]} {a[2]}'
        if op=='copy': return ex(a[0])
        return f'({ex(a[0])} {"+" if op=="add" else "*"} {ex(a[1])})'
    ce=ex(CE[t])
    evs=sorted(set(v for q in ceat for v in (parse_atom(RAW[q])[1][1:] if parse_atom(RAW[q])[0] in ('add','mul') else []) if v in evvar))
    L=[]
    L.append(f'/-- Table {t}\'s air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ`, times its form value. -/')
    L.append(f'theorem vtAir{t} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ){" {ev : ℕ → E}" if evs else ""}')
    if evs: L.append(f'    (hev : ∀ c < {WIDTH[t]}, σ (.n (vtEvB ({BASE[t]} + c))) = ev c)')
    L.append(f'    : σ (.n 5817) = σ (.n {x}) * σ (.n {tau}) ∧ LoadHolds rd (σ (.n 10)) {t+1} (σ (.n {tau})) ∧')
    L.append(f'      LoadHolds rd (σ (.n 5915) * σ (.n {x})) 0 (σ (.n {cp})) ∧')
    L.append(f'      LoadHolds rd (σ (.n 5936) * σ (.n {tau})) 0 (σ (.n {pe})) ∧')
    L.append(f'      σ (.n {air}) = σ (.n {cp}) * σ (.n {pe}) *')
    L.append(f'        {ce} := by')
    poss=[pm,ptau,pcpb,pcp,ppeb,ppe,pw,pa]+sorted(ceat)
    for q in poss: L.append(at(q))
    L.append('  simp only [Atom.Holds] at '+' '.join(f'a{q}' for q in poss))
    for v in evs:
        k=evvar[v]; c=k-BASE[t]
        L.append(f'  have v{v} : σ (.n {v}) = ev {c} := by')
        L.append(f'    rw [← hev {c} (by norm_num)]; exact (vt_eval h (k := {k}) (by norm_num)).2.2.1')
    rw=' '.join([])
    L.append(f'  refine ⟨a{pm}, a{ptau}, by rw [← a{pcpb}]; exact a{pcp}, by rw [← a{ppeb}]; exact a{ppe}, ?_⟩')
    ceq=[f'a{q}' for q in sorted(ceat,reverse=True)]+[f'v{v}' for v in evs]
    L.append(f'  rw [a{pa}, a{pw}, '+wrapl(', '.join(ceq),'    ',90)+']')
    out.append('\n'.join(L))
# total
chainp=[]
v=11197
while v not in airs:
    p,op,a=D[v]; chainp.append(p); v=a[0]
L=[]
L.append('/-- **The air check**: the sumcheck\'s final claim is the six tables\' air terms\' sum. -/')
L.append('theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :')
L.append('    σ (.n 5933) = '+' + '.join(f'σ (.n {a})' for a in airs)+' := by')
poss=chainp+[10208]
for q in poss: L.append(at(q))
L.append('  simp only [Atom.Holds] at '+' '.join(f'a{q}' for q in poss))
L.append('  rw [eq_neg_of_add_eq_zero_right a10208, CharTwo.neg_eq, '+', '.join(f'a{q}' for q in chainp)+']')
out.append('\n'.join(L))
write('Air',"`verify_tables`' air check: each table's weight and form value, and their sum the table\n  sumcheck's final claim.",'LeanVM.Guest.B1.Tables.Vt.FormsVal\npublic import LeanVM.Guest.B1.Tables.Vt.Pi','\n\n'.join('set_option maxRecDepth 10000 in\n'+x for x in out))
