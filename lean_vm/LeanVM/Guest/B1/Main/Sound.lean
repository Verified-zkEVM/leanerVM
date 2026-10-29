/-
  LeanVM.Guest.B1.Main.Sound

  B1 for `main` (G:4063-4231; TRIAGE #96): a run of `main`'s body establishes `NodeRel` of the
  seed, the statement and the witness its decoders read.
-/

module

public import LeanVM.Guest.B1.Main.Digests

/-!
# `main`, soundly, its witness decoded

`main_sound_w`: `main_sound_Spec bytecode` (`Main/Interface`), given `exponent_tables`' statement
(B1-a). From a run of the body (`main_facts`), the children's records (`kid_rec`), the coverage
table's writers (`writers`) and its bijection (`cover_bij`):

* the statement's digest (`own_digest`): the bytes `statement_digest` hashes are the decoded
  statement's (`statementDigest_parts`), and its two cells are the public input's;
* each child's statement's digest (`kid_digest`), so each child's proof is the deferring
  verifier's on the decoded child's statement (`verify_sub`'s contract);
* every declared signature claim's holder, by the mark in its slot: a raw signature's check or
  the child whose segment holds the mark (`xmss_held`, `sphincs_held`);
* the DA digest, by the slot `da_pick`: the direct DA check's claim, zeros, or a child's
  (`da_rel`);
* the deferred claim: the leaf's zero point, or the batching (`aggregate_claims`' contract).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec} {sl : ℕ → ℕ}

theorem digestBytes_decSeed (σ : Val) :
    digestBytes (decSeed σ) = cellsBytes [σ (.n 47), σ (.n 48)] := digestBytes_ofCells _ _

theorem gLog_lg (σ : Val) (v : ℕ) : gLog (σ (.n v)) = lg σ v := (lg_eq_gLog σ v).symm

/-! ## The statement's digest -/

/-- The DA digest at the slot `da_pick` holds the cells `statement_digest` reads. -/
theorem pick_cells (MF : MainFacts C rd σ) :
    LoadHolds rd (σ (.n 334)) (2 * lg σ 387) (σ (.n 429)) ∧
      LoadHolds rd (σ (.n 334)) (2 * lg σ 387 + 1) (σ (.n 430)) := by
  obtain ⟨h0, h1⟩ := MF.dacells
  rw [MF.picked, loadHolds_gen_pow_iff] at h0 h1
  rw [Nat.add_zero] at h0
  exact ⟨h0, h1⟩

/-- **The decoded statement's digest** is the one `statement_digest` computes. -/
theorem own_digest (MF : MainFacts C rd σ) :
    [σ (.n 431), σ (.n 432)] = digestCells (statementDigest (decSeed σ) (decStmt σ rd)) := by
  obtain ⟨cells, hlen, hreads, -, hrets⟩ := statement_digest_sound rd _ _ MF.stmt
  obtain ⟨cx, hlx, hrx, -, hdx⟩ := MF.xlist
  obtain ⟨cs, hls, hrs, -, hds⟩ := MF.slist
  have hx := xmss_digest_id (slotsHold_of_readsAt hrx hlx)
  have hs := sphincs_digest_id (slotsHold_of_readsAt hrs hls)
  obtain ⟨p0, p1⟩ := pick_cells MF
  have eX : (decStmt σ rd).claims.xmss = (List.range (lg σ 0)).map (xmssAt rd (σ (.n 53))) := by
    unfold decStmt; simp only [gLog_lg]
  have eS : (decStmt σ rd).claims.sphincs =
      (List.range (lg σ 3)).map (sphincsAt rd (σ (.n 56))) := by
    unfold decStmt; simp only [gLog_lg]
  have eD : (decStmt σ rd).claims.da = daDigestAt rd σ (lg σ 387) := by
    unfold decStmt; simp only [gLog_lg]
  have hdef : (decStmt σ rd).defer.cells = cells := by
    unfold decStmt; simp only; rw [readCells_of_readsAt hreads hlen]; exact deferOfCells_cells hlen
  have hxd : digestBytes (claimListDigest (decStmt σ rd).claims.xmss) =
      cellsBytes [σ (.n 57), σ (.n 58)] := by
    rw [eX, hx]; exact digestBytes_of_cells hdx
  have hsd : digestBytes (claimListDigest (decStmt σ rd).claims.sphincs) =
      cellsBytes [σ (.n 59), σ (.n 60)] := by
    rw [eS, hs]; exact digestBytes_of_cells hds
  have hda : digestBytes (decStmt σ rd).claims.da = cellsBytes [σ (.n 429), σ (.n 430)] := by
    rw [eD]; exact (daDigestAt_of_loads p0 p1).2
  rw [hrets, statementDigest_parts (digestBytes_decSeed σ) hxd hsd hda hdef hlen]

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec} {sl : ℕ → ℕ}

/-! ## A child's statement's digest -/

/-- **Child `c`'s statement's digest** is the one its `statement_digest` call computes. -/
theorem kid_digest (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c))
    (hW : Writers rd (σ (.n 67)) (segsOf σ K) (LXS σ) (LSS σ))
    (hC : Cover rd (σ (.n 67)) (segsOf σ K) (LXS σ) (LSS σ) sl) {c : ℕ}
    (hc : c < lg σ 6) :
    [(K c).p0, (K c).p1] = digestCells (statementDigest (decSeed σ) (kidStmt rd σ c)) := by
  have k := hK c hc
  rw [kidStmt_eq MF hK hW hC hc]
  have hx := xmss_digest (o := (K c).ox) (n := (K c).ex) (p := σ (.n 53))
    ⟨k.xlen, fun j hj i hi => (k.xrec j hj).2.2 i hi⟩
  have hs := sphincs_digest (o := (K c).os) (n := (K c).es) (p := σ (.n 56))
    ⟨k.slen, fun j hj i hi => (k.srec j hj).2.2 i hi⟩
  have hxd : digestBytes (claimListDigest
      ((List.range (K c).ex).map fun j => xmssAt rd (σ (.n 53)) ((K c).ox j))) =
      cellsBytes [(K c).cx0, (K c).cx1] := by
    rw [hx]; exact digestBytes_of_cells k.xdig
  have hsd : digestBytes (claimListDigest
      ((List.range (K c).es).map fun j => sphincsAt rd (σ (.n 56)) ((K c).os j))) =
      cellsBytes [(K c).cs0, (K c).cs1] := by
    rw [hs]; exact digestBytes_of_cells k.sdig
  have hda := (daDigestAt_of_loads k.da0 k.da1).2
  have hdef : (deferOfCells (readCells rd (σ (.n 377) * gen ^ (24 * c)) 24)).cells = (K c).defer := by
    rw [readCells_of_readsAt k.defreads k.deflen]; exact deferOfCells_cells k.deflen
  have hst := statementDigest_parts (seed := decSeed σ)
    (s := ⟨⟨(List.range (K c).ex).map fun j => xmssAt rd (σ (.n 53)) ((K c).ox j),
        (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 56)) ((K c).os j),
        daDigestAt rd σ c⟩,
       deferOfCells (readCells rd (σ (.n 377) * gen ^ (24 * c)) 24)⟩)
    (digestBytes_decSeed σ) hxd hsd hda hdef k.deflen
  rw [k.pdig, hst]

end
end LeanVM.Guest.B1.Main
