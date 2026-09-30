#!/usr/bin/env python3
"""Merge codes-class.tsv (letter codes) and layer.tsv (Layer N) into one verdict table.
Output columns: verdict, file:line, token, replacement, context.
verdict: VIOLATION / CHECK (a table cell: allowed only in an index column) / allowed:<why>."""
import re
LAYER = {0:'the field instances',1:'tables and stacking',2:'Clean expressions as polynomials',3:'the adaptor (the leanISA instance)',
 4:'the sumcheck and batching components',5:'fingerprints and the grand-product GKR',6:'the bus phase',7:'the table sumcheck',
 8:'the public-input phase',9:'the Flock phase',10:'the claim pool and the opening',11:'WHIR and Merkle trees',
 12:'the compilation and the executable verifier',13:'the base theorems and fixtures'}
T = {1:'arithmetization and ISA equivalence',2:'witness-generator correctness',3:'exact guest correctness',
 4:'base proof extraction and completeness',5:'recursive-verifier correctness',6:'recursion extraction',
 7:'end-to-end soundness',8:'end-to-end completeness'}
AT = {1:'fingerprint degree',2:'padding leaves are 1',3:'the nonzero count root is load-bearing',4:'one root, not two',5:'domain separators',
 6:'zerocheck point recycling',7:'back-loaded padding',8:'degree three, three scalars',9:'shared bus powers',10:'top limb of the public input',
 11:'joint list binding',12:'absorb before squeeze',13:'index column bit order',14:'bytecode slot bits',15:'selector alignment',16:'variable order',
 17:'radix and parity',18:'counts in the count tree',19:'the extractor reads the stack',20:'no exceptional challenge',21:'sizes are parameters',
 22:'tags, not labels',23:'numeric error',24:'the extractor computes',25:'the import rule holds',26:'seams are the contract',
 27:'the toy instance is honest',28:'the bus seam bounds the degree'}
DEC = {1:'heights are powers of two',2:'statement and parameters',3:'where the zerocheck is charged',4:'where generic code lives',
 5:'an end-to-end run of the honest prover',6:'the witness is the stack',7:'phases over an abstract instance',8:'five clauses, caps outside',
 9:'balance is a permutation',10:'worst-case round-by-round knowledge soundness',11:'extractors are computable definitions',
 12:'the strong Flock predicate',13:'public lines, not cells',14:'the degree bound belongs to the instance',15:'the public-input transcript'}
HOLE = {'S':'the spine','C1':'the knowledge-soundness composition','L1':'tables and stacking','I1':'Clean expressions as polynomials','I2':'the adaptor',
 'G1':'sumcheck: definition and completeness','G2':'sumcheck: knowledge soundness','G3':'batching by powers','G4':'fingerprint and collision bound',
 'G5':'grand-product GKR: definition and completeness','G6':'grand-product GKR: knowledge soundness','P1':'bus phase: definition and completeness',
 'P2':'bus phase: knowledge soundness','P3':'table sumcheck: definition and completeness','P4':'table sumcheck: knowledge soundness',
 'P5':'the public-input phase','P6':'the Flock phase','P7':'opening: definition and completeness','P8':'opening: knowledge soundness',
 'K1':'the WHIR opening','K2':'Merkle trees, byte hasher, WHIR parameters','K3':'transcript, proof object, compiled verifier','K4':'the base theorems'}
OWNROW = {'checks-bus.tex':'B','transcript-bus.tex':'SCU','transcript-table-pub.tex':'TP','checks-opening.tex':'RGMW'}
INV_DP = [(133,160),(167,205),(208,236),(238,283),(290,380)]   # docs-proposal.tex code tables
def repl(tok):
    m = re.match(r'Layers?[ ~](\d+)', tok)
    if m and not tok.startswith('Layers'): return f"{LAYER.get(int(m.group(1)),'?')} (Layer {m.group(1)})"
    if tok.startswith('Layers'): return 'name each layer, numbers in parentheses: "the bus and table phases (Layers 6 and 7)"'
    m = re.fullmatch(r'T(\d)', tok)
    if m and int(m.group(1)) in T: return f"{T[int(m.group(1))]} (T{m.group(1)}), unless it is a transcript step of table 8.6"
    m = re.match(r'acceptance tests? (\d+)', tok)
    if m: return f"the acceptance test \"{AT.get(int(m.group(1)),'?')}\" (acceptance test {m.group(1)})"
    m = re.match(r'[Dd]ecisions? (\d+)', tok)
    if m: return f"the decision \"{DEC.get(int(m.group(1)),'?')}\" (decision {m.group(1)})"
    m = re.match(r'[Hh]oles? (\S+)', tok)
    if m: return f"the hole \"{HOLE.get(m.group(1),'?')}\" ({m.group(1)})"
    if tok in HOLE: return f"if a hole: \"{HOLE[tok]}\" ({tok}); if a dossier locator: gt-… §X.n or \\cref to the finding box"
    return 'name the thing in words; code in parentheses after the name, or drop it'
out = []
ROOT='../../tex/'
_cache={}
def line(f,l):
    if f not in _cache: _cache[f]=open(ROOT+f,encoding='utf-8').read().split('\n')
    return _cache[f][l-1]
def inquote(f,l,tok):
    s=line(f,l); i=s.find(tok)
    while i!=-1:
        pre=s[:i]
        q = pre.count('``')>pre.count("''")
        j=pre.rfind('\\enquote{')
        if j!=-1:
            seg=pre[j:]
            if seg.count('{')>seg.count('}'): q=True
        if q: return True
        i=s.find(tok,i+1)
    return False
SUBJECT=('docs-contradictions.tex','docs-codes.tex','docs-inventory.tex','docs-vocabulary.tex','docs-proposal.tex','docs-texts.tex','code-index.tex')
for ln in open('codes-class.tsv', encoding='utf-8'):
    c, loc, tok, ctx = ln.rstrip('\n').split('\t', 3)
    if tok.startswith('Layer'): continue              # Layer handled from layer.tsv
    f, l = loc.rsplit(':', 1); l = int(l); b = f.split('/')[-1]
    pre = ctx.split('[[')[0]
    if c == 'reg': v = 'allowed:register row' if not (b in OWNROW and 'R' in OWNROW[b]) else 'VIOLATION:own row code colliding with the register'
    elif c == 'inventory': v = 'allowed:code inventory'
    elif b == 'docs-proposal.tex' and any(a <= l <= z for a, z in INV_DP): v = 'allowed:code inventory (ch.12 mapping tables)'
    elif c == 'cmd': v = 'allowed:identifier or file name'
    elif inquote(f,l,tok): v = 'allowed:quotation'
    elif b in SUBJECT: v = 'allowed:subject matter (the documents\' codes discussed or quoted)'
    elif b in OWNROW and tok[0] in OWNROW[b] and pre.strip() in ('', '\\textbf{'): v = 'VIOLATION:own row code (collides)'
    elif pre.count('``') > pre.count("''") or '\\enquote{' in pre[-80:]: v = 'allowed:quotation'
    elif c == 'paren':
        s=line(f,l); i=s.find(tok); pre=s[:i].rstrip() if i!=-1 else ''
        v = 'allowed:parenthesised' if pre.endswith('(') or pre.endswith('\\texttt{') else 'CHECK:inside a parenthetical, not right after a name'
    elif b == 'register.tex' and re.fullmatch(r'[NU]\d+', tok) and 'textbf{[[' in ctx: v = 'allowed:register row'
    else: v = 'VIOLATION'
    out.append((v, loc, tok, repl(tok), ctx))
for ln in open('layer.tsv', encoding='utf-8'):
    c, loc, tok, ctx = ln.rstrip('\n').split('\t', 3)
    f2,l2=loc.rsplit(':',1)
    if c in ('prose','cell','heading') and inquote(f2,int(l2),tok): c='quote'
    v = {'heading':'VIOLATION:heading','prose':'VIOLATION','cell':'CHECK:table cell','paren':'allowed:parenthesised','quote':'allowed:quotation'}[c]
    if c=='paren':
        s=line(f2,int(l2)); i=s.find(tok); pre=s[:i].rstrip() if i!=-1 else ''
        if not pre.endswith('('): v='CHECK:inside a parenthetical, not right after a name'
    out.append((v, loc, tok, repl(tok), ctx))
out.sort(key=lambda r: (r[1].rsplit(':',1)[0], int(r[1].rsplit(':',1)[1])))
with open('codes-verdict.tsv', 'w', encoding='utf-8') as w:
    w.write('verdict\tfile:line\ttoken\treplacement\tcontext\n')
    for r in out: w.write('\t'.join(r) + '\n')
import collections
cnt = collections.Counter(r[0].split(':')[0] for r in out); print(cnt, len(out))
cnt2 = collections.Counter(r[0] for r in out); 
for k,v in cnt2.most_common(): print(v, k)
