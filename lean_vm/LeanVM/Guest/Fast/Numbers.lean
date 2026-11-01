module

public import LeanVM.Guest.B1.Sig.SphincsT

/-!
# Template positions, as numbers

The definitions the literal tables of `Fast/*Tables.lean` are checked against, arithmetic in the
template's parameters, with no statement built: a codeword's arms, selectors and chain starts
(`walkBaseN` … `startN`, `offTab`, proved equal to the generators in `Fast/Wots.lean`), the
forest keys' chains and arms (`fkChainN` … `fkOffN`) and the folds' arms (`foldPos`,
`Fast/SphincsN.lean`). The checks import these and the templates alone (`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## A codeword -/

/-- The base of walk `r + j` of arm `k` from walk `r` at `b` (`walkBase`). -/
def walkBaseN (stride k : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, b => b
  | r, j + 1, b => walkBaseN stride k (r + 1) j (b + walkSize stride (k / 4 ^ r % 4))


/-- The base after arm `k` from `a`, of a step of size `sz` (`armNext`). -/
def armNextN (sz n : ℕ) (fold : Bool) (k a : ℕ) : ℕ :=
  if k = 0 then walkBaseN (sz + 13) k 0 n (if fold then a + 1 else a) + 2
  else walkBaseN sz k 0 n (if fold then a + 1 else a) + 1

/-- The base of arm `k + j` from arm `k` at `b` (`armBase`). -/
def armBaseN (sz n : ℕ) (fold : Bool) : ℕ → ℕ → ℕ → ℕ
  | _, 0, b => b
  | k, j + 1, b => armBaseN sz n fold (k + 1) j (armNextN sz n fold k b)

/-- The selector cell of group `p` of a codeword from `b` (`(cwState W b p).2.2`). -/
def selN (sz b : ℕ) : ℕ → ℕ
  | 0 => b
  | p + 1 => armBaseN sz 3 (p == 0) 0 64 (selN sz b p + 5)

/-- The slot of chain `r`'s step `s` in a group from `b` (`slotsT`). -/
def slotsN (sz : ℕ) (fold : Bool) (b r s : ℕ) : ℕ :=
  b + 5 + (if fold then 1 else 0) + (1 + 3 * (sz + 13)) * r + 1 + (sz + 13) * s + sz

/-- **Chain `r`'s start** in arm `k` of a group of `n` digits whose selector is `sel`. -/
def startN (sz n : ℕ) (fold : Bool) (sel k r : ℕ) : ℕ :=
  if k / 4 ^ r % 4 = 3 then slotsN sz fold sel r 2
  else walkBaseN (if k = 0 then sz + 13 else sz) k 0 r
    (if fold then armBaseN sz n fold 0 k (sel + 5) + 1 else armBaseN sz n fold 0 k (sel + 5))

/-! ## Tables -/

/-- Entry `k` of row `r`. -/
def offAt (tab : List (List ℕ)) (r k : ℕ) : ℕ := (tab.getD r []).getD k 0

/-- The table of a group of `n` digits: row `r`, entry `k`, the start of chain `r` in arm `k`
from selector `0`. -/
def offTab (sz n : ℕ) (fold : Bool) : List (List ℕ) :=
  (List.range n).map fun r ↦ (List.range (4 ^ n)).map fun k ↦ startN sz n fold 0 k r

/-- A scheme's three tables: the first group's, the other groups', the last chain's. -/
structure WotsTabs (sz : ℕ) (first rest last : List (List ℕ)) : Prop where
  first : first = offTab sz 3 true
  rest : rest = offTab sz 3 false
  last : last = offTab sz 1 false

/-! ## The forest keys and the folds -/

/-- The base after chain `i` of key `t` from `b` (`fkChain`). -/
def fkChainN (t i b : ℕ) : ℕ :=
  if spCode t i = 0 then b + 1
  else if i < 2 then b + 1 + 15 * spCode t i else b + 2 + 15 * spCode t i

/-- The base after chains `i ..< i + m` of key `t` from `b` (`fkChains`). -/
def fkChainsN (t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, b => b
  | m + 1, i, b => fkChainsN t m (i + 1) (fkChainN t i b)

/-- The base of arm `t` of the 256 from `b` (`fkAB`). -/
def fkABN : ℕ → ℕ → ℕ
  | 0, b => b
  | t + 1, b => fkChainsN t 6 0 (fkABN t b) + (if t = 0 then 17 else 15)

/-- Chain `i` of arm `t`, from the arms' base `0`. -/
def fkOffN (t i : ℕ) : ℕ := fkChainsN t i 0 (fkABN t 0)

/-- The base of arm `a` of a fold from `b`, its first arm `first` cells, the others `rest`. -/
def foldPos (first rest b a : ℕ) : ℕ := if a = 0 then b else b + first + rest * (a - 1)

end
end LeanVM.Guest.Fast
