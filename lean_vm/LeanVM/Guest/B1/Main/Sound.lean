/-
  LeanVM.Guest.B1.Main.Sound

  B1 for `main` (G:4086-4282; TRIAGE #96): a run of `main`'s body establishes `NodeRel` of the
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
* every declared claim's holder, by the mark in its slot: a raw signature's check, the direct DA
  check, or the child whose segment holds the mark (`xmss_held`, `sphincs_held`, `da_held`);
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
    digestBytes (decSeed σ) = cellsBytes [σ (.n 63), σ (.n 64)] := digestBytes_ofCells _ _

theorem gLog_lg (σ : Val) (v : ℕ) : gLog (σ (.n v)) = lg σ v := (lg_eq_gLog σ v).symm

/-! ## The statement's digest -/

/-- **The decoded statement's digest** is the one `statement_digest` computes. -/
theorem own_digest (MF : MainFacts C rd σ) :
    [σ (.n 424), σ (.n 425)] = digestCells (statementDigest (decSeed σ) (decStmt σ rd)) := by
  obtain ⟨cells, hlen, hreads, -, hrets⟩ := statement_digest_sound rd _ _ MF.own
  obtain ⟨cx, hlx, hrx, -, hdx⟩ := MF.xlist
  obtain ⟨cs, hls, hrs, -, hds⟩ := MF.slist
  obtain ⟨cd, hld, hrd, -, hdd⟩ := MF.dalist
  have hx := xmss_digest_id (slotsHold_of_readsAt hrx hlx)
  have hs := sphincs_digest_id (slotsHold_of_readsAt hrs hls)
  have hd := da_digest_id (slotsHold_of_readsAt hrd hld)
  have eX : (decStmt σ rd).claims.xmss = (List.range (lg σ 0)).map (xmssAt rd (σ (.n 77))) := by
    unfold decStmt; simp only [gLog_lg]
  have eS : (decStmt σ rd).claims.sphincs =
      (List.range (lg σ 3)).map (sphincsAt rd (σ (.n 80))) := by
    unfold decStmt; simp only [gLog_lg]
  have eD : (decStmt σ rd).claims.da = (List.range (lg σ 40)).map (daAt rd (σ (.n 69))) := by
    unfold decStmt; simp only [gLog_lg]
  have hdef : (decStmt σ rd).defer.cells = cells := by
    unfold decStmt; simp only; rw [readCells_of_readsAt hreads hlen]; exact deferOfCells_cells hlen
  have hxd : digestBytes (claimListDigest (decStmt σ rd).claims.xmss) =
      cellsBytes [σ (.n 81), σ (.n 82)] := by
    rw [eX, hx]; exact digestBytes_of_cells hdx
  have hsd : digestBytes (claimListDigest (decStmt σ rd).claims.sphincs) =
      cellsBytes [σ (.n 83), σ (.n 84)] := by
    rw [eS, hs]; exact digestBytes_of_cells hds
  have hda : digestBytes (daListDigest (decStmt σ rd).claims.da) = cellsBytes [σ (.n 73), σ (.n 74)] := by
    rw [eD, hd]; exact digestBytes_of_cells hdd
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

theorem kid_slots_d {c : ℕ} (k : KidOk C rd σ c (K c)) :
    SlotsHold rd (σ (.n 69)) (K c).di (K c).ed (K c).cellsd := by
  refine ⟨k.dlen, fun d hd i hi => ?_⟩
  obtain ⟨hl4, -, -, hload, hreads⟩ := k.drec d hd
  have h1 := hload i hi
  have h2 := hreads i (by omega)
  have h3 := k.dreads (4 * d + i) (by rw [k.dlen]; omega)
  rw [loadHolds_mul_gen_pow] at h2
  have e := loadHolds_unique h2 h3
  have e1 : (K c).cellsd.getD (4 * d + i) 0 = (K c).cellsd[4 * d + i]'(by rw [k.dlen]; omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [k.dlen]; omega),
      Option.getD_some]
  have e2 : ((K c).dr d).getD i 0 = ((K c).dr d)[i]'(by omega) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [e1, ← e, ← e2]
  exact h1

/-- **Child `c`'s statement's digest** is the one its `statement_digest` call computes. -/
theorem kid_digest (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c))
    (hW : Writers rd (σ (.n 97)) (segsOf σ K) (LXS σ) (LSS σ) (DAS σ))
    (hC : Cover rd (σ (.n 97)) (segsOf σ K) (LXS σ) (LSS σ) (DAS σ) sl) {c : ℕ}
    (hc : c < lg σ 6) :
    [(K c).p0, (K c).p1] = digestCells (statementDigest (decSeed σ) (kidStmt rd σ c)) := by
  have k := hK c hc
  rw [kidStmt_eq MF hK hW hC hc]
  have hx := xmss_digest (o := (K c).ox) (n := (K c).ex) (p := σ (.n 77))
    ⟨k.xlen, fun j hj i hi => (k.xrec j hj).2.2 i hi⟩
  have hs := sphincs_digest (o := (K c).os) (n := (K c).es) (p := σ (.n 80))
    ⟨k.slen, fun j hj i hi => (k.srec j hj).2.2 i hi⟩
  have hd := da_digest (kid_slots_d k)
  have hxd : digestBytes (claimListDigest
      ((List.range (K c).ex).map fun j => xmssAt rd (σ (.n 77)) ((K c).ox j))) =
      cellsBytes [(K c).cx0, (K c).cx1] := by
    rw [hx]; exact digestBytes_of_cells k.xdig
  have hsd : digestBytes (claimListDigest
      ((List.range (K c).es).map fun j => sphincsAt rd (σ (.n 80)) ((K c).os j))) =
      cellsBytes [(K c).cs0, (K c).cs1] := by
    rw [hs]; exact digestBytes_of_cells k.sdig
  have hda : digestBytes (daListDigest
      ((List.range (K c).ed).map fun d => daAt rd (σ (.n 69)) ((K c).di d))) =
      cellsBytes [(K c).d0, (K c).d1] := by
    rw [hd]; exact digestBytes_of_cells k.ddig
  have hdef : (deferOfCells (readCells rd (σ (.n 386) * gen ^ (24 * c)) 24)).cells = (K c).defer := by
    rw [readCells_of_readsAt k.defreads k.deflen]; exact deferOfCells_cells k.deflen
  have hst := statementDigest_parts (seed := decSeed σ)
    (s := ⟨⟨(List.range (K c).ex).map fun j => xmssAt rd (σ (.n 77)) ((K c).ox j),
        (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 80)) ((K c).os j),
        (List.range (K c).ed).map fun d => daAt rd (σ (.n 69)) ((K c).di d)⟩,
       deferOfCells (readCells rd (σ (.n 386) * gen ^ (24 * c)) 24)⟩)
    (digestBytes_decSeed σ) hxd hsd hda hdef k.deflen
  rw [k.pdig, hst]

end
end LeanVM.Guest.B1.Main
