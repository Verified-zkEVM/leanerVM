/-
  LeanVM.Guest.B1.Digest.Interface

  The interface of B1's digest functions (the statement's digest, the claim lists' digests, the
  DA root list's digest, a DA slot's coverage): what each computes, and the statements that its
  core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Sponge
public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Sphincs.Scheme
public import LeanVM.Fast.Schemes
public import LeanDa.Scheme
public import LeanVM.Fast.Da
public import LeanVM.Fast.Keccak
public import LeanVM.Fast.CubicExt
public import LeanVM.Fast.FieldWords
public import LeanVM.Facts.Verifier

/-!
# The digests: meanings (TRIAGE G #86-89, #94, #95)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM
`3375f7a13`, G below) its meaning `Meaning…` on its argument and return words, and two
statements on its core IR relation (`coreProgram.Rel`): `…_sound_Spec`, the relation gives the
meaning, and `…_complete_Spec`, the meaning (with what memory an honest run holds) gives the
relation. A `…_Spec` is a definition (a `Prop`); its proof is the theorem `…_holds` of the
family's modules.

| function | G | core | meaning |
| --- | --- | --- | --- |
| `statement_digest` | 3766-3797 | `core21` | Keccak-256 of the six header cells and the 24 deferred cells, three limbs each (`statementDigest`, N:197) |
| `list_split` | 3812-3824 | `core22` | `n = 17 · groups + rest`, `groups < 2^16`, `rest < 17` |
| `claim_list_digest` | 3827-3849 | `core23` | Keccak-256 of the `4n` canonical cells of the list (`xmssListDigest`, `sphincsListDigest`, N:172-180) |
| `child_claim_list_digest` | 3876-3903 | `core24` | the same over cells read at hinted slots of this node's table, each slot marked in the coverage table |
| `da_list_digest` | 4063-4075 | `core29` | Keccak-256 of the `4n` canonical cells of `n ≤ 16` DA claims (`daListDigest`, N:187) |
| `cover_da_root` | 4078-4083 | `core30` | a hinted DA slot, below the bound, marked; its four cells |

**Cells and bytes.** A cell holds sixteen bytes, limbs `0` and `1` (`Value.Keccak.cellsBytes`;
the `KECCAK` instruction makes every cell it reads canonical, `AllCanonical`). A digest's two
cells are `digestScalars` (`digestCells`); a deferred cell is a full field element, hashed as its
three limbs (`Node.eBytes`, `pack_pair`).

**The memory.** A range check (`assert log x < log b`) is an exact relation on the memory read
(`RangeChecked`); on a memory image of `2^κ` words, `16 ≤ κ ≤ 32` (`MemOk`, as every valid
execution's is), it says `x = g^e` with `e` below the bound's log (`BelowLog`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Shared vocabulary -/

/-- The reader is a memory image of `2^κ` words, `16 ≤ κ ≤ 32`, as every valid execution's is. -/
def MemOk (rd : Reader) : Prop := ∃ κ, 16 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemImage κ, rd = L.read

/-- A digest's two cells (`digestScalars`), as a list. -/
def digestCells (d : Digest) : List E := [(digestScalars d).1, (digestScalars d).2]

/-- `x = g^e` with `e` below the log of the bound `b`, as a range check against `b · g⁻¹`
establishes on a memory image of at most `2^32` words: `b = g^(e + e' + 1)`, `e, e' < 2^32`. -/
def BelowLog (b : E) (e : ℕ) : Prop := e < 2 ^ 32 ∧ ∃ e' < 2 ^ 32, b = gen ^ (e + e' + 1)

/-- `g⁻¹`, the word a runtime range bound is multiplied by (`assert log x < log b`). -/
abbrev ginvW : E := word 9223372036854775821 0 0

/-! ## `statement_digest` (G:3766-3797, TRIAGE #86) -/

/-- `DEFER_STMT_CELLS`: the cells of a statement's deferred claim, `BYTECODE_VARS = 23`
coordinates and the value. -/
abbrev deferStmtCells : ℕ := 24

/-- The bytes `statement_digest` hashes: the header cells (seed, signer-set digest, DA list
digest), then the deferred cells, three limbs each. `24` is even: no zero partner. -/
def stmtBytes (hdr defer : List E) : List UInt8 := cellsBytes hdr ++ defer.flatMap Node.eBytes

/-- **`statement_digest(seed_0, seed_1, signers_hash, da_0, da_1, defer)`**: the signer-set
digest's two cells at `signers_hash`, the 24 deferred cells at `defer`; the six header cells are
canonical (the `KECCAK` reads them), and the function returns the two cells of the Keccak-256
digest of the header cells and the deferred cells' limbs. -/
def MeaningStatementDigest (rd : Reader) : List E → List E → Prop
  | [s0, s1, sp, a0, a1, dp], rets => ∃ h0 h1 : E, ∃ cells : List E,
      LoadHolds rd sp 0 h0 ∧ LoadHolds rd sp 1 h1 ∧ cells.length = deferStmtCells ∧
      ReadsAt rd dp cells ∧ AllCanonical [s0, s1, h0, h1, a0, a1] ∧
      rets = digestCells (keccak256 (stmtBytes [s0, s1, h0, h1, a0, a1] cells))
  | _, _ => False

/-- `statement_digest`'s core IR gives its meaning. -/
def statement_digest_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "statement_digest" args rets → MeaningStatementDigest rd args rets

/-- `statement_digest`'s meaning gives its core IR. -/
def statement_digest_complete_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    MeaningStatementDigest rd args rets → coreProgram.Rel rd "statement_digest" args rets

/-! ## `list_split` (G:3812-3824, TRIAGE #87) -/

/-- `CLAIM_GROUP`: claims hashed a loop frame. -/
abbrev claimGroup : ℕ := 17

/-- `MAX_KEYS`. -/
abbrev maxKeys : ℕ := 65536

/-- **`list_split(n_g)`**: `n_g = g^(17 a + b)` with `a < 2^16`, `b < 17`, and the function returns
`g^a`, `g^b`. -/
def MeaningListSplit : List E → List E → Prop
  | [ng], rets => ∃ a < maxKeys, ∃ b < claimGroup, ng = gen ^ (claimGroup * a + b) ∧
      rets = [gen ^ a, gen ^ b]
  | _, _ => False

/-- `list_split`'s core IR gives its meaning, on a memory image. -/
def list_split_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "list_split" args rets → MeaningListSplit args rets

/-- `list_split`'s meaning gives its core IR, on a memory image. -/
def list_split_complete_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    MeaningListSplit args rets → coreProgram.Rel rd "list_split" args rets

/-! ## `claim_list_digest` (G:3827-3861, TRIAGE #88) -/

/-- The `4n` cells of `n` claims at `entries` are canonical, and `rets` is the two cells of their
Keccak-256 digest (an empty list: the empty string's). -/
def ClaimListOut (rd : Reader) (entries : E) (n : ℕ) (rets : List E) : Prop :=
  ∃ cells : List E, cells.length = 4 * n ∧ ReadsAt rd entries cells ∧ AllCanonical cells ∧
    rets = digestCells (keccak256 (cellsBytes cells))

/-- **`claim_list_digest(entries, n_g)`**: `n_g = g^n` for a count `n < 17 · 2^16`, and the
function returns the digest of the `n` claims at `entries` (`ClaimListOut`). -/
def MeaningClaimListDigest (rd : Reader) : List E → List E → Prop
  | [entries, ng], rets => ∃ n < claimGroup * maxKeys, ng = gen ^ n ∧ ClaimListOut rd entries n rets
  | _, _ => False

/-- `claim_list_digest`'s core IR gives its meaning, on a memory image. -/
def claim_list_digest_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "claim_list_digest" args rets → MeaningClaimListDigest rd args rets

/-! ## `child_claim_list_digest` (G:3864-3917, TRIAGE #89) -/

/-- **A child's claim list rebuilt from this node's table**: claim `j < n` sits at slot `o j` of
the table at `entries` (its four cells at `entries · g^(4 o j)`), the slot below the log of `limit`
and marked in the coverage table, `cover[origin · g^(o j)] = base · g^j`; the `4n` cells are
canonical and `rets` is the two cells of their Keccak-256 digest. -/
def ChildListOut (rd : Reader) (entries cover base origin limit : E) (n : ℕ) (rets : List E) :
    Prop :=
  ∃ (o : ℕ → ℕ) (cells : List E), cells.length = 4 * n ∧ AllCanonical cells ∧
    (∀ j < n, BelowLog limit (o j) ∧ LoadHolds rd (cover * (origin * gen ^ o j)) 0 (base * gen ^ j) ∧
      ∀ c < 4, LoadHolds rd entries (4 * o j + c) (cells.getD (4 * j + c) 0)) ∧
    rets = digestCells (keccak256 (cellsBytes cells))

/-- **`child_claim_list_digest(entries, cover, base, origin_g, limit_g, n_g)`**: `n_g = g^n`,
`n < 17 · 2^16`, and the function returns the digest of the claims rebuilt at hinted slots
(`ChildListOut`). -/
def MeaningChildClaimListDigest (rd : Reader) : List E → List E → Prop
  | [entries, cover, base, origin, limit, ng], rets => ∃ n < claimGroup * maxKeys,
      ng = gen ^ n ∧ ChildListOut rd entries cover base origin limit n rets
  | _, _ => False

/-- `child_claim_list_digest`'s core IR gives its meaning, on a memory image. -/
def child_claim_list_digest_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "child_claim_list_digest" args rets →
      MeaningChildClaimListDigest rd args rets

/-! ## `da_list_digest` (G:4063-4075, TRIAGE #94) -/

/-- `MAX_DA_ROOTS`. -/
abbrev maxDaRoots : ℕ := 16

/-- **`da_list_digest(roots, n_g)`**: `n_g = g^n`, `n ≤ 16` (the dispatch), the `4n` cells at
`roots` are canonical, and the function returns the two cells of their Keccak-256 digest. -/
def MeaningDaListDigest (rd : Reader) : List E → List E → Prop
  | [roots, ng], rets => ∃ n ≤ maxDaRoots, ng = gen ^ n ∧ ClaimListOut rd roots n rets
  | _, _ => False

/-- `da_list_digest`'s core IR gives its meaning. -/
def da_list_digest_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_list_digest" args rets → MeaningDaListDigest rd args rets

/-- `da_list_digest`'s meaning gives its core IR. -/
def da_list_digest_complete_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    MeaningDaListDigest rd args rets → coreProgram.Rel rd "da_list_digest" args rets

/-! ## `cover_da_root` (G:4078-4083, TRIAGE #95) -/

/-- **`cover_da_root(roots, cover, n_slots_g, mark)`**: a slot `i` below the log of `n_slots_g`,
`cover[g^i] = mark`, and the function returns the four words at `roots · g^(4i)`. -/
def MeaningCoverDaRoot (rd : Reader) : List E → List E → Prop
  | [roots, cover, nslots, mark], rets => ∃ i, BelowLog nslots i ∧ LoadHolds rd cover i mark ∧
      rets.length = 4 ∧ ∀ c < 4, LoadHolds rd roots (4 * i + c) (rets.getD c 0)
  | _, _ => False

/-- `cover_da_root`'s core IR gives its meaning, on a memory image. -/
def cover_da_root_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "cover_da_root" args rets → MeaningCoverDaRoot rd args rets

/-! ## The functions, found -/

theorem find_statement_digest : coreProgram.find? "statement_digest" = some Data.core21 :=
  Program.find?_of_indexOf? (j := 21) (by decide +kernel) rfl

theorem find_list_split : coreProgram.find? "list_split" = some Data.core22 :=
  Program.find?_of_indexOf? (j := 22) (by decide +kernel) rfl

theorem find_claim_list_digest : coreProgram.find? "claim_list_digest" = some Data.core23 :=
  Program.find?_of_indexOf? (j := 23) (by decide +kernel) rfl

theorem find_child_claim_list_digest :
    coreProgram.find? "child_claim_list_digest" = some Data.core24 :=
  Program.find?_of_indexOf? (j := 24) (by decide +kernel) rfl

theorem find_da_list_digest : coreProgram.find? "da_list_digest" = some Data.core29 :=
  Program.find?_of_indexOf? (j := 29) (by decide +kernel) rfl

theorem find_cover_da_root : coreProgram.find? "cover_da_root" = some Data.core30 :=
  Program.find?_of_indexOf? (j := 30) (by decide +kernel) rfl

end
end LeanVM.Guest.B1.Digest
