# usage: python3 -I genbglue.py > ../../LeanVM/Guest/B1/Tables/VtC/BGlueGen.lean
# verify_tables' bus sides between the selectors and stream reads: one lemma per slice, the
# statements beyond evaluation by kind (weight, block_kappa, pool, index-buffer reads; kappa range
# checks), the others (stores, dispatches, the KECCAK) taken as hypotheses.
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vtflat
top, flat, ctr, cend = vtflat.load()
tctr = {}
for (k, s), c in zip(flat, ctr): tctr.setdefault(k, c)
SLICES = [(2404, 2407), (2424, 2434), (2452, 2462), (2471, 2476), (2485, 2490), (2499, 2510),
          (2528, 2586), (3484, 3910), (3910, 3938), (3947, 3983), (3992, 4305), (5098, 5152)]
READ = {14: 'hw', 12: 'hbkc', 16: 'hpool', 2851: 'hidx'}
def auto(s):
    m = re.match(r'\.atom \(\.(\w+)', s)
    if not m: return False
    op = m.group(1)
    if op in ('const', 'add', 'copy', 'hint'): return True
    if op == 'mul':
        v = [int(x) for x in re.findall(r'\.n (\d+)', s)]
        return v[1] < v[0] and v[2] < v[0]
    return False
def lean(s):
    # vt_ir statements are Lean terms already; lists in dispatch use '::' form - keep
    return s
out = []
for a, b in SLICES:
    rest = []; proofs = []; specials = []; used = set()
    for k in range(a, b):
        s = top[k]
        if auto(s): continue
        mi = re.match(r'\.dispatch \(\.n (\d+)\) \("index_mle__L0" :: .*\) \[\.n 8\] \[\.n (\d+)\]$', s)
        if mi:
            s = f'.dispatch (.n {mi.group(1)}) vtImNames [.n 8] [.n {mi.group(2)}]'
            top[k] = s
        rest.append(s)
        mem = f'(vtB_memAt {k} _ (by decide +kernel))'
        m = re.match(r'\.atom \(\.load \(\.n (\d+)\) \(\.n (\d+)\) (\d+)\)$', s)
        if m and int(m.group(1)) >= tctr[k] and int(m.group(2)) in READ:
            d, p, off = map(int, m.groups())
            proofs.append(f'(vtB_readM hl {mem} (by decide +kernel) ({READ[p]} {off} (by norm_num))).2')
            used.add(READ[p])
            continue
        m = re.match(r'\.atom \(\.rangeCheck \(\.n (\d+)\) \(\.n (\d+)\) \(\.n (\d+)\) \(\.n (\d+)\) \(\.n (\d+)\)\)$', s)
        if m:
            x, y, t1, t2, kk = map(int, m.groups())
            m2 = re.match(r'\.atom \(\.load \(\.n (\d+)\) \(\.n 12\) (\d+)\)$', top[k - 2])
            m3 = re.match(r'\.atom \(\.const \(\.n (\d+)\) \(word 8589934592 0 0\)\)$', top[k - 1])
            assert m2 and int(m2.group(1)) == x and m3 and int(m3.group(1)) == kk, (k, s)
            bb = int(m2.group(2))
            used.update(['hbkc', 'hκ', 'hlow'])
            proofs.append(f'vshB_rcM hl {mem} (by simp) (K := 34)\n'
                          f'      (vtB_readM hl (vtB_memAt {k-2} _ (by decide +kernel)) (by decide +kernel) (hbkc {bb} (by norm_num))).1\n'
                          f'      (by rw [vtB_const hl (vtB_memAt {k-1} (.atom (.const (.n {kk}) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ {bb} (by norm_num)) hlow')
            continue
        specials.append(k)
        proofs.append(f'h{k}')
    name = f'vtB_glue_{a}'
    hyps = ''.join(f'\n    (h{k} : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) ({top[k]}))' for k in specials)
    restl = ',\n    '.join(rest)
    if rest:
        body = (f'  refine vtB_blockR hl {a} {b - a} [\n    {restl}] (by decide +kernel) ?_\n'
                f'  intro s hs hm\n'
                f'  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs\n'
                f'  rcases hs with {" | ".join(["rfl"] * len(rest))}\n' +
                ''.join(f'  · exact {p}\n' for p in proofs))
    else:
        body = f'  exact vtB_blockR hl {a} {b - a} [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))\n'
    H = ''
    if 'hw' in used: H += '{W : ℕ → E}\n    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) '
    if 'hbkc' in used: H += '{κ : ℕ → ℕ}\n    (hbkc : ∀ b < 153, LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ κ b))\n    (hκ : ∀ b < 153, κ b < 34) '
    if 'hpool' in used: H += '{P : ℕ → E}\n    (hpool : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 16)) i (P i)) '
    if 'hidx' in used: H += '{Q : ℕ → E}\n    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 2851)) i (Q i)) '
    if 'hlow' in used: H += '\n    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome)'
    sys.stderr.write(f'{name}: {sorted(used)} specials {specials}\n')
    out.append(f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem {name} (hl : args.length = 22) {H}{hyps} :
    ∀ s ∈ (vtPre.drop {a}).take {b - a}, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
{body}''')
print('''/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides between the selectors and the stream reads, slice by slice
  (generated: scripts/b1c-vt/genbglue.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BGlue
public import LeanVM.Guest.B1.Tables.Vt.SelFw

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

theorem vtB_w33 : word 8589934592 0 0 = gen ^ (34 - 1) := word_g33.trans (gen_pow_eq_ofK 33).symm

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}
''')
print('\n'.join(out))
print('''end

end
end LeanVM.Guest.B1.Tables''')
