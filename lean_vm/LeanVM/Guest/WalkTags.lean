/-
  LeanVM.Guest.WalkTags

  The tags of the guest's semantic relations (`Glob.sem`), and the relations of the windowed
  Merkle walk's tags.
-/

module

public import LeanVM.Guest.B1.Opening.WalkDefs

/-!
# The tags of the semantic relations

A function's precondition names tuples of its frame cells in relations by tag (`Check.Sig.sem`):

* `0`: the exponent table (`B1.ExpTables`) at the tuple's one word (`verify_sub`, `__loop4`);
* `1` (`Check.tagNe`): the two words differ, the checker's own (a loop's `x ≠ N`);
* `walkTag kind odd d cd`: the windows `opening_queries`' walk dispatches on, specialization
  `(odd, base, depth d, cap_depth cd)` (`lean_ethereum.py:1380-1404` at `c4f4bc92`): `kind` `0`
  `WinWalk` on `[t, x, N]` (a deeper loop), `1` `WinWalk2` on `[t, x, N]` (a level-0 loop), `2 + base`
  `OqMainWins` on `[t, N]` (the function's window pointers and iteration count).

`walkSem t` is the relation of tag `t ≥ 2`, decoded by `walkKind`, `walkOdd`, `walkD`, `walkCd`.
The certificates' generator (`cli/GuestCert.lean`) writes the tags.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

/-- The tag of a walk relation, `kind < 4`, `cd < 64`. -/
def walkTag (kind odd d cd : ℕ) : ℕ := 2 + kind + 4 * (odd + 2 * (cd + 64 * d))

/-- A walk tag's kind. -/
def walkKind (t : ℕ) : ℕ := (t - 2) % 4

/-- A walk tag's `odd`. -/
def walkOdd (t : ℕ) : ℕ := (t - 2) / 4 % 2

/-- A walk tag's `cap_depth`. -/
def walkCd (t : ℕ) : ℕ := (t - 2) / 8 % 64

/-- A walk tag's depth. -/
def walkD (t : ℕ) : ℕ := (t - 2) / 512

/-- **The relation of walk tag `t`** on the words `ws`. -/
def walkSem (t : ℕ) (rd : Reader) (ws : List E) : Prop :=
  match walkKind t with
  | 0 => B1.WinWalk rd (walkD t) (walkCd t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  | 1 => B1.WinWalk2 rd (walkD t) (walkCd t) (walkOdd t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  | k => B1.OqMainWins rd (walkD t) (walkCd t) (walkOdd t) (k - 2) (ws.getD 0 0) (ws.getD 1 0)

theorem walkTag_decode {kind odd d cd : ℕ} (hk : kind < 4) (ho : odd < 2) (hc : cd < 64) :
    walkKind (walkTag kind odd d cd) = kind ∧ walkOdd (walkTag kind odd d cd) = odd ∧
      walkD (walkTag kind odd d cd) = d ∧ walkCd (walkTag kind odd d cd) = cd := by
  unfold walkKind walkOdd walkD walkCd walkTag
  refine ⟨by omega, by omega, by omega, by omega⟩

end
end LeanVM.Guest
