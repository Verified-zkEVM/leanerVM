#!/usr/bin/env python3
"""Classify every 'Layer N' / 'Layers N..' / 'Layer~N' outside verbatim. Classes:
 paren: inside an open '(' ; quote: inside ``..'' or \\enquote{..} ; heading: on a \\(sub)*section/\\chapter/\\caption/\\paragraph line ;
 cell: on a line containing '&' (a table row) ; prose: the rest."""
import re, glob, os, sys
root=sys.argv[1]
vb=re.compile(r'\\begin\{(leancode|srccode|shellcode|Verbatim|verbatim)\}');ve=re.compile(r'\\end\{(leancode|srccode|shellcode|Verbatim|verbatim)\}')
pat=re.compile(r'Layers?[ ~]\d+')
for f in sorted(glob.glob(root+'/sections/*.tex')+glob.glob(root+'/sections/gen/*.tex')):
    b=os.path.basename(f)
    if b.startswith('index-'): continue
    inv=False
    for n,s in enumerate(open(f,encoding='utf-8'),1):
        if vb.search(s): inv=True
        if inv:
            if ve.search(s): inv=False
            continue
        if s.lstrip().startswith('%'): continue
        for m in pat.finditer(s):
            pre=s[:m.start()]
            # quote state
            q = pre.count('``')>pre.count("''") or (pre.rfind('\\enquote{')>-1 and pre[pre.rfind('\\enquote{'):].count('{')>pre[pre.rfind('\\enquote{'):].count('}'))
            # paren state: last unmatched '(' in pre (same line)
            depth=0; 
            for ch in pre:
                if ch=='(': depth+=1
                elif ch==')' and depth>0: depth-=1
            if q: c='quote'
            elif depth>0: c='paren'
            elif re.search(r'\\(chapter|section|subsection|subsubsection|paragraph|caption)\*?[\[{]', s): c='heading'
            elif '&' in s: c='cell'
            else: c='prose'
            print(f"{c}\t{os.path.relpath(f,root)}:{n}\t{m.group(0)}\t{s[max(0,m.start()-60):m.end()+40].strip()}")
