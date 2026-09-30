#!/usr/bin/env python3
"""Measure the audit surface of the two master theorems.

For each load-bearing declaration (list E below, class C = needed by both theorems,
Kx = additionally by the knowledge theorem in either form, K = by the knowledge theorem in the
`With` form only), find it by name in its file, take its extent up to the next blank line, the
docstring block right before it, and count: code lines (no blank, no comment, and for `def`s no
proof field), and all lines (declaration with its docstring and field docstrings)."""
import re, collections
ROOT='/home/scaraven/Documents/Verified-zkEVM/leanerVM/'
PROOF_FIELDS={'complete','rbr','toFun_empty','toFun_next','toFun_full','verify_eq','read_eval',
              'mle_eq','constraints_degree','flushes_degree','hEq','outputInterface_heq'}
E=[('LeanerVM/Protocol/Field.lean','C',['structure Column','def limbsEquiv','instance instSampleableTypeE','instance evalOracle']),
 ('LeanerVM/Protocol/ToArkLib/Oracles.lean','C',['abbrev NoOracle','abbrev OneOracle']),
 ('LeanerVM/Protocol/Spine/Instance.lean','C',['inductive Side','structure Shape','abbrev Shape.ColumnId','structure Layout','inductive Coord','structure BoundaryBlock','structure PublicLine','structure M3Instance','attribute [instance] M3Instance.decAux','abbrev κ','def column','def row','def coordCell','def flushTuples','def boundaryTuples','def tuples','def ConstraintsVanish','def Balanced','def CountsNonzero','def PublicLinesHold','def M3Holds','abbrev TheOracle','def M3Rel']),
 ('LeanerVM/Protocol/Spine/Seams.lean','C',['structure ColumnClaim','def ColumnClaim.Holds','structure VirtualTerm','def VirtualTerm.table','def VirtualTerm.eval','structure LinearClaim','def LinearClaim.Holds','structure Weight','def Weight.pair','structure WeightedClaim','def WeightedClaim.Holds','structure BusOut','structure TableOut','structure PubOut','structure FlockOut','abbrev theStack','def of','def commit','def bus','def table','def pub','def flock','def done']),
 ('LeanerVM/Protocol/ToArkLib/Component.lean','C',['structure Def','attribute [instance] Def.msgOracle','structure Complete','def Def.append']),
 ('LeanerVM/Protocol/ToArkLib/Component.lean','Kx',['structure Security']),
 ('LeanerVM/Protocol/ToArkLib/Component.lean','K',['def stateFunctionOfEq','def guardedAppend','def Complete.append','def Security.append']),
 ('LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean','K',['abbrev Witness','theorem witness_left','theorem witness_right','def left','def right','def state','def appendGuarded']),
 ('LeanerVM/Protocol/ToArkLib/SendOracle.lean','C',['def sendSpec','def sendProver','def sendEmbedding','def sendVerifier','def sendOracle']),
 ('LeanerVM/Protocol/ToArkLib/SendOracle.lean','K',['def sendOracle_relOut','def sendVerifierPure','def sendOracleComplete','abbrev sendWitMid','def sendExtractor','def sendStateFunction','def sendOracleSecurity']),
 ('LeanerVM/Protocol/Spine/Phase.lean','C',['abbrev Def','abbrev Complete']),
 ('LeanerVM/Protocol/Spine/Phase.lean','Kx',['abbrev Security']),
 ('LeanerVM/Protocol/Spine/Compose.lean','C',['abbrev commitSpec','abbrev commitDef','structure Phases where','def Phases.toDef','structure Phases.Complete','def leanVmPiop','theorem piop_perfectCompleteness']),
 ('LeanerVM/Protocol/Spine/Compose.lean','Kx',['structure Phases.Security','def leanVmVerifier','def piopError','theorem piop_rbrKnowledgeSoundness_exists']),
 ('LeanerVM/Protocol/Spine/Compose.lean','K',['abbrev commitExtractor','def commitComplete','def commitSecurity','def Phases.Security.toDef','def piopExtractor','theorem piop_rbrKnowledgeSoundness']),
]
def find(L, key):
    pat=re.compile(r'^(@\[[^\]]*\]\s*)?(private |noncomputable |public )*'+re.escape(key)+r'(\b|$)')
    hits=[i for i,l in enumerate(L) if pat.match(l)]
    # also allow attribute lines that precede (e.g. @[reducible] on its own line)
    assert len(hits)==1, (key, hits)
    i=hits[0]
    # attribute on the previous line
    if i>0 and L[i-1].strip().startswith('@['): i-=1
    j=i
    while j+1<len(L) and L[j+1].strip()!='': j+=1
    # docstring before
    d0=None
    k=i-1
    if k>=0 and L[k].strip().endswith('-/'):
        while k>=0 and not L[k].strip().startswith('/--'): k-=1
        d0=k
    return i,j,d0
rows=[]
for f,cls,keys in E:
    L=__import__("subprocess").run(["git","-C",ROOT,"show","b435631:"+f],capture_output=True,text=True).stdout.split("\n")
    for key in keys:
        i,j,d0=find(L,key)
        isdef=not key.startswith(('structure','inductive','attribute'))
        code=0; total=0; indoc=False; inproof=False
        for n in range(i,j+1):
            t=L[n].strip()
            total+=1
            if indoc:
                if t.endswith('-/'): indoc=False
                continue
            if t.startswith('/--') or t.startswith('/-'):
                if not t.endswith('-/'): indoc=True
                continue
            if t.startswith('--'): continue
            if isdef:
                m=re.match(r'^(\w+)\s*(:=|\|)',t)
                if m and m.group(1) in PROOF_FIELDS: inproof=True; continue
                if m and m.group(1) not in PROOF_FIELDS: inproof=False
                if inproof and (t.startswith('·') or t.startswith('(') or not re.match(r'^\w+\s*:=',t)): continue
            code+=1
        if d0 is not None: total+=i-d0
        rows.append((f.split('/')[-1],key,cls,code,total,i+1,j+1))
per=collections.defaultdict(lambda:[0,0,0,0])
for fn,key,cls,code,total,a,b in rows:
    print(f'{cls:2} {code:3} {total:3}  {fn:20} {a:4}-{b:<4} {key}')
    per[fn][{'C':0,'Kx':1,'K':2}[cls]]+=code; per[fn][3]+=total
print('\nper file: code lines C / Kx / K ; all lines with docstrings')
for fn,v in per.items(): print(f'{fn:22} {v[0]:4} {v[1]:4} {v[2]:4}   {v[3]:4}')
def tot(cs): return (sum(r[3] for r in rows if r[2] in cs), sum(r[4] for r in rows if r[2] in cs), len([r for r in rows if r[2] in cs]))
print('\ncompleteness theorem (C):                   code %d, with docstrings %d, declarations %d'%tot('C'))
print('knowledge theorem, existential form (C+Kx): code %d, with docstrings %d, declarations %d'%tot(('C','Kx')))
print('knowledge theorem, With form (C+Kx+K):      code %d, with docstrings %d, declarations %d'%tot(('C','Kx','K')))
