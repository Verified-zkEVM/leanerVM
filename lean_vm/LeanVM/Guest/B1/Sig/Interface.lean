/-
  LeanVM.Guest.B1.Sig.Interface

  What the signature verifiers of the aggregation guest establish, as named statements: the
  interface `main`'s proof composes, the proofs landing under the same names.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.CoreLemmas
public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Sphincs.Equations
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier

/-!
# The signature verifiers' interface

`verify_lean_xmss(signer)` (`lean_ethereum.py:3446-3514`, core function `Data.core19`) and
`verify_sig_lean_sphincs(signer, byte_bits)` (`lean_ethereum.py:3627-3753`, `Data.core20`) check
one signature of the claim at `signer`: four cells, the key's root and parameter, then the
message's two halves, the low first. Both call nothing (every helper is `@inline` and every
`match` arm runs in the frame), so their relation is their body's under any call relation.

**The decoding of a claim.** A cell `c` is the 128-bit value of its two low limbs, limb `0` the
low (`cellVal`; the `KECCAK` instructions that read the cells make them canonical); the message is
the two cells, the first low (`cellPairVal`). `xmssClaimOf a b c d`, `sphincsClaimOf a b c d` are
the claims of the four cells, as `Node.XmssClaim`, `Node.SphincsClaim`.

**What a call establishes for a signature** (`XmssOut rd p sig`, `SphincsOut rd p sig`): the four
words at `p` are a claim that `sig` verifies under Keccak-256 (`Node.xmssVerify`,
`Node.sphincsVerify`). `XmssSigned`, `SphincsSigned` are their existentials.

**The statements** (`…_Spec`, each a `Prop`; the proofs land as `…_holds`):

* `verify_lean_xmss_sound_Spec sigOf`: whenever the body holds of a valuation `σ`, it returns no
  words and `sigOf σ`, the signature read off the valuation, verifies the claim at its argument.
  The decoder of the end theorem reads the signature this way, through the frame of the call.
* `verify_sig_lean_sphincs_sound_Spec sigOf`: the same for leanSPHINCS, on a memory image of at most
  `2^32` words (the range checks of `sp_from_bytes` are bounded discrete logarithms there,
  `rangeCheck_iff`), when its `byte_bits` argument holds the table `main` writes (`ByteBits`:
  `byte_bits[g^v] = v`, `lean_ethereum.py:4138-4140`): the counter is then a 32-bit integer, so the
  encoding hash's 292 bytes are the scheme's.
* `verify_lean_xmss_complete_Spec`, `verify_sig_lean_sphincs_complete_Spec`: for a claim held at `p`
  in its canonical cells and a signature that verifies it, on a memory of at least `64`
  (leanXMSS) or `256` (leanSPHINCS, with the byte table) words, so that every range check has its
  witnesses, the body holds of some valuation with the call's arguments, under any call relation.

From them, the call relation (`coreProgram.Rel`) gives the claim signed (`verify_lean_xmss_signed`,
`verify_sig_lean_sphincs_signed`) and holds of every signed claim (`verify_lean_xmss_rel`,
`verify_sig_lean_sphincs_rel`): proved here, from the `Spec`s as hypotheses.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Cells as the schemes' values -/

/-- A cell's 128-bit value: limb `0` the low 64 bits, limb `1` the high (limb `2` dropped). -/
def cellVal (c : E) : BitVec 128 := (c.limb 1).toBitVec ++ (c.limb 0).toBitVec

/-- The canonical cell of a 128-bit value. -/
def cellOf128 (v : BitVec 128) : E :=
  E.ofLimbs (BF64.ofBitVec (v.extractLsb' 0 64)) (BF64.ofBitVec (v.extractLsb' 64 64)) 0

/-- The 256-bit value of two cells, the first low. -/
def cellPairVal (lo hi : E) : BitVec 256 := cellVal hi ++ cellVal lo

/-- The leanXMSS claim of four cells: the key's root and parameter, the message's halves. -/
def xmssClaimOf (a b c d : E) : Node.XmssClaim := (⟨cellVal a, cellVal b⟩, cellPairVal c d)

/-- The leanSPHINCS claim of four cells. -/
def sphincsClaimOf (a b c d : E) : Node.SphincsClaim := (⟨cellVal a, cellVal b⟩, cellPairVal c d)

/-- The four words at `p`: `a`, `b`, `c`, `d` at offsets `0` to `3`. -/
def ClaimAt (rd : Reader) (p a b c d : E) : Prop :=
  LoadHolds rd p 0 a ∧ LoadHolds rd p 1 b ∧ LoadHolds rd p 2 c ∧ LoadHolds rd p 3 d

/-! ## What a call establishes -/

/-- **What `verify_lean_xmss(p)` establishes for the signature `sig`**: the four words at `p` are a
leanXMSS claim that `sig` verifies under Keccak-256. -/
def XmssOut (rd : Reader) (p : E) (sig : LeanXmss.Signature) : Prop :=
  ∃ a b c d, ClaimAt rd p a b c d ∧
    Node.xmssVerify (xmssClaimOf a b c d).1 (xmssClaimOf a b c d).2 sig = true

/-- **What `verify_sig_lean_sphincs(p, _)` establishes for the signature `sig`**: the four words at
`p` are a leanSPHINCS claim that `sig` verifies under Keccak-256. -/
def SphincsOut (rd : Reader) (p : E) (sig : Sphincs.Signature) : Prop :=
  ∃ a b c d, ClaimAt rd p a b c d ∧
    Node.sphincsVerify (sphincsClaimOf a b c d).1 (sphincsClaimOf a b c d).2 sig = true

/-- Some leanXMSS signature verifies the claim at `p`. -/
def XmssSigned (rd : Reader) (p : E) : Prop := ∃ sig, XmssOut rd p sig

/-- Some leanSPHINCS signature verifies the claim at `p`. -/
def SphincsSigned (rd : Reader) (p : E) : Prop := ∃ sig, SphincsOut rd p sig

/-! ## Preconditions -/

/-- **The byte table** `main` writes (`lean_ethereum.py:4138-4140`): `byte_bits[g^v] = v` for every
byte `v`, the word whose bits spell `v`. -/
def ByteBits (rd : Reader) (bb : E) : Prop := ∀ v < 256, LoadHolds rd bb v (word v 0 0)

/-- The memory holds a word at each of the first `n` addresses `g^i`: a range check below `n` has
its witnesses. -/
def MemOK (rd : Reader) (n : ℕ) : Prop := ∀ i < n, (rd (gpow i)).isSome

/-! ## The statements -/

/-- **`verify_lean_xmss` is sound, for the signature `sigOf` reads off its valuation**: whenever its
body holds of `σ` (under any call relation: it calls nothing), it returns no words and `sigOf σ`
verifies the claim at its argument `σ (.n 0)`. -/
def verify_lean_xmss_sound_Spec (sigOf : Val → LeanXmss.Signature) : Prop :=
  ∀ (C : CallRel) (rd : Reader) (σ : Val) (rets : List E),
    Stmt.HoldsList C rd σ Data.core19.body False (fun rs => rs = rets) →
      rets = [] ∧ XmssOut rd (σ (.n 0)) (sigOf σ)

/-- **`verify_sig_lean_sphincs` is sound, for the signature `sigOf` reads off its valuation**: on a
memory image of at most `2^32` words, whenever its body holds of `σ`, it returns no words, and
when its second argument `σ (.n 1)` holds the byte table, `sigOf σ` verifies the claim at its
first argument `σ (.n 0)`. -/
def verify_sig_lean_sphincs_sound_Spec (sigOf : Val → Sphincs.Signature) : Prop :=
  ∀ (C : CallRel) {κ : ℕ} (L : MemoryImage κ), κ ≤ 32 → ∀ (σ : Val) (rets : List E),
    Stmt.HoldsList C L.read σ Data.core20.body False (fun rs => rs = rets) →
      rets = [] ∧ (ByteBits L.read (σ (.n 1)) → SphincsOut L.read (σ (.n 0)) (sigOf σ))

/-- **`verify_lean_xmss` is complete**: for a claim held at `p` in its canonical cells and a
signature that verifies it, on a memory of at least `64` words, the body holds of some valuation
whose argument is `p`, under any call relation. -/
def verify_lean_xmss_complete_Spec : Prop :=
  ∀ (C : CallRel) (rd : Reader) (p : E) (pk : LeanXmss.PublicKey) (m : LeanXmss.Message)
    (sig : LeanXmss.Signature), MemOK rd 64 →
    ClaimAt rd p (cellOf128 pk.root) (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)) →
    Node.xmssVerify pk m sig = true →
      ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsList C rd σ Data.core19.body False (fun rs => rs = [])

/-- **`verify_sig_lean_sphincs` is complete**: for a claim held at `p` in its canonical cells and a
signature that verifies it, on a memory of at least `256` words with the byte table at `bb`, the
body holds of some valuation whose arguments are `p` and `bb`, under any call relation. -/
def verify_sig_lean_sphincs_complete_Spec : Prop :=
  ∀ (C : CallRel) (rd : Reader) (p bb : E) (pk : Sphincs.PublicKey) (m : Sphincs.Message)
    (sig : Sphincs.Signature), MemOK rd 256 → ByteBits rd bb →
    ClaimAt rd p (cellOf128 pk.root) (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)) →
    Node.sphincsVerify pk m sig = true →
      ∃ σ : Val, σ (.n 0) = p ∧ σ (.n 1) = bb ∧
        Stmt.HoldsList C rd σ Data.core20.body False (fun rs => rs = [])

/-! ## The functions, found -/

theorem core19_params : Data.core19.params = [.n 0] := rfl

theorem core20_params : Data.core20.params = [.n 0, .n 1] := rfl

theorem find_verify_lean_xmss : coreProgram.find? "verify_lean_xmss" = some Data.core19 :=
  Program.find?_of_indexOf? (j := 19) (by decide +kernel) rfl

theorem find_verify_sig_lean_sphincs :
    coreProgram.find? "verify_sig_lean_sphincs" = some Data.core20 :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

/-! ## The call relation, from the statements -/

variable {rd : Reader}

theorem rel_iff_body {name : String} {fn : Fn} (h : coreProgram.find? name = some fn)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [rel_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.Sem]

/-- **A call of `verify_lean_xmss`** takes one argument, returns nothing, and the claim at the
argument is signed. -/
theorem verify_lean_xmss_signed {sigOf : Val → LeanXmss.Signature}
    (hs : verify_lean_xmss_sound_Spec sigOf) {args rets : List E}
    (h : coreProgram.Rel rd "verify_lean_xmss" args rets) :
    ∃ p, args = [p] ∧ rets = [] ∧ XmssSigned rd p := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_body find_verify_lean_xmss args rets).mp h
  obtain ⟨hr, ho⟩ := hs _ _ _ _ hb
  exact ⟨σ (.n 0), by rw [← hp]; rfl, hr, _, ho⟩

/-- **A call of `verify_sig_lean_sphincs`** on a memory image of at most `2^32` words takes two
arguments, returns nothing, and when the second holds the byte table the claim at the first is
signed. -/
theorem verify_sig_lean_sphincs_signed {sigOf : Val → Sphincs.Signature}
    (hs : verify_sig_lean_sphincs_sound_Spec sigOf) {κ : ℕ} {L : MemoryImage κ} (hκ : κ ≤ 32)
    {args rets : List E} (h : coreProgram.Rel L.read "verify_sig_lean_sphincs" args rets) :
    ∃ p bb, args = [p, bb] ∧ rets = [] ∧ (ByteBits L.read bb → SphincsSigned L.read p) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_body find_verify_sig_lean_sphincs args rets).mp h
  obtain ⟨hr, ho⟩ := hs _ L hκ σ rets hb
  exact ⟨σ (.n 0), σ (.n 1), by rw [← hp]; rfl, hr, fun hbb => ⟨_, ho hbb⟩⟩

/-- **`verify_lean_xmss` holds of every signed claim** in its canonical cells, on a memory of at
least `64` words. -/
theorem verify_lean_xmss_rel (hc : verify_lean_xmss_complete_Spec) {p : E}
    {pk : LeanXmss.PublicKey} {m : LeanXmss.Message} {sig : LeanXmss.Signature} (hrd : MemOK rd 64)
    (hat : ClaimAt rd p (cellOf128 pk.root) (cellOf128 pk.parameter)
      (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.xmssVerify pk m sig = true) :
    coreProgram.Rel rd "verify_lean_xmss" [p] [] := by
  obtain ⟨σ, hσ, hb⟩ := hc _ rd p pk m sig hrd hat hv
  exact (rel_iff_body find_verify_lean_xmss [p] []).mpr ⟨σ, by simp [core19_params, hσ], hb⟩

end
end LeanVM.Guest.B1.Sig
