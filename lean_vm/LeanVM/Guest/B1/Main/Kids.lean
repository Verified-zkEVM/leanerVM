/-
  LeanVM.Guest.B1.Main.Kids

  What each child of `main` establishes, its records named: the digest family's statements
  applied to the calls of `__loop5`.
-/

module

public import LeanVM.Guest.B1.Main.Cover
public import LeanVM.Guest.B1.Digest.Statement

/-!
# The children's records

`KidStep` (`__loop5`'s iteration) names the calls; with the digest family's statements
(`child_claim_list_digest_sound`, `cover_da_root_sound`, `da_list_digest_sound`,
`statement_digest_sound`) each child's records are values (`KidRec`) with their facts (`KidOk`):
its leanXMSS and leanSPHINCS claims' slots and cells, its DA roots' slots and words, its lists'
digests, its statement's digest at `child_pi`, its proof's check, and the running counts.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- A child's records. -/
structure KidRec where
  base : E
  sp : E
  cx0 : E
  cx1 : E
  cs0 : E
  cs1 : E
  d0 : E
  d1 : E
  p0 : E
  p1 : E
  cda : E
  ex : ℕ
  es : ℕ
  ed : ℕ
  ox : ℕ → ℕ
  cellsx : List E
  os : ℕ → ℕ
  cellss : List E
  di : ℕ → ℕ
  dr : ℕ → List E
  cellsd : List E
  h0 : E
  h1 : E
  defer : List E

/-- **What child `c` establishes.** -/
structure KidOk (rd : Reader) (σ : Val) (c : ℕ) (k : KidRec) : Prop where
  base : LoadHolds rd (σ (.n 409)) c k.base
  next : LoadHolds rd (σ (.n 409)) (c + 1) (k.base * (gen ^ k.ex * gen ^ k.es) * gen ^ k.ed)
  bounds : k.ex ≤ 65535 ∧ k.es ≤ 65535 ∧ k.ed ≤ 16
  xlen : k.cellsx.length = 4 * k.ex
  xcan : AllCanonical k.cellsx
  xrec : ∀ j < k.ex, BelowLog (σ (.n 55)) (k.ox j) ∧
    LoadHolds rd (σ (.n 117) * (1 * gen ^ k.ox j)) 0 (k.base * gen ^ j) ∧
    ∀ i < 4, LoadHolds rd (σ (.n 77)) (4 * k.ox j + i) (k.cellsx.getD (4 * j + i) 0)
  xdig : [k.cx0, k.cx1] = digestCells (keccak256 (cellsBytes k.cellsx))
  slen : k.cellss.length = 4 * k.es
  scan : AllCanonical k.cellss
  srec : ∀ j < k.es, BelowLog (σ (.n 56)) (k.os j) ∧
    LoadHolds rd (σ (.n 117) * (σ (.n 55) * gen ^ k.os j)) 0 (k.base * gen ^ k.ex * gen ^ j) ∧
    ∀ i < 4, LoadHolds rd (σ (.n 80)) (4 * k.os j + i) (k.cellss.getD (4 * j + i) 0)
  sdig : [k.cs0, k.cs1] = digestCells (keccak256 (cellsBytes k.cellss))
  sig0 : LoadHolds rd k.sp 0 (digestScalars (keccak256 (cellsBytes [k.cx0, k.cx1, k.cs0, k.cs1]))).1
  sig1 : LoadHolds rd k.sp 1 (digestScalars (keccak256 (cellsBytes [k.cx0, k.cx1, k.cs0, k.cs1]))).2
  sigcan : AllCanonical [k.cx0, k.cx1, k.cs0, k.cs1]
  drec : ∀ d < k.ed, (k.dr d).length = 4 ∧ BelowLog (σ (.n 50)) (k.di d) ∧
    LoadHolds rd (σ (.n 118)) (k.di d) (k.base * (gen ^ k.ex * gen ^ k.es) * gen ^ d) ∧
    (∀ i < 4, LoadHolds rd (σ (.n 69)) (4 * k.di d + i) ((k.dr d).getD i 0)) ∧
    ReadsAt rd (k.cda * gen ^ (4 * d)) (k.dr d)
  dlen : k.cellsd.length = 4 * k.ed
  dreads : ReadsAt rd k.cda k.cellsd
  dcan : AllCanonical k.cellsd
  ddig : [k.d0, k.d1] = digestCells (keccak256 (cellsBytes k.cellsd))
  h0 : LoadHolds rd k.sp 0 k.h0
  h1 : LoadHolds rd k.sp 1 k.h1
  deflen : k.defer.length = 24
  defreads : ReadsAt rd (σ (.n 406) * gen ^ (24 * c)) k.defer
  hdrcan : AllCanonical [σ (.n 63), σ (.n 64), k.h0, k.h1, k.d0, k.d1]
  pdig : [k.p0, k.p1] =
    digestCells (keccak256 (stmtBytes [σ (.n 63), σ (.n 64), k.h0, k.h1, k.d0, k.d1] k.defer))
  pi0 : LoadHolds rd (σ (.n 394)) (2 * c) k.p0
  pi1 : LoadHolds rd (σ (.n 394)) (2 * c + 1) k.p1
  sub : coreProgram.Rel rd "verify_sub"
    [k.p0, k.p1, σ (.n 63), σ (.n 64), σ (.n 65), σ (.n 66), σ (.n 400) * gen ^ (24 * c)] []

theorem loadHolds_gen_pow_iff {rd : Reader} {p : E} {c k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ c) k w ↔ LoadHolds rd p (c + k) w :=
  loadHolds_mul_gen_pow rd p c k w

/-- **Each child's records.** -/
theorem kid_rec {rd : Reader} (hm : MemOk rd) {σ : Val} (MF : MainFacts rd σ) :
    ∀ c < lg σ 6, ∃ k : KidRec, KidOk rd σ c k := by
  intro c hc
  obtain ⟨base, sp, cx0, cx1, cs0, cs1, d0, d1, p0, p1, cda, ex, es, ed, hb, hex, hes, hed, hcx,
    hcs, hcan, hsp0, hsp1, hdas, hdl, hsd, hp0, hp1, hsub, hnext⟩ := MF.children c hc
  -- the leanXMSS records
  obtain ⟨nx, hnx, hgx, ox, cellsx, hlx, hcanx, hrecx, hdigx⟩ :=
    child_claim_list_digest_sound rd hm _ _ hcx
  have hnx' : nx < 1114112 := hnx
  have hexn := gen_pow_inj34 (by omega) (by omega) hgx
  subst hexn
  -- the leanSPHINCS records
  obtain ⟨ns, hns, hgs, os, cellss, hls, hcans, hrecs, hdigs⟩ :=
    child_claim_list_digest_sound rd hm _ _ hcs
  have hns' : ns < 1114112 := hns
  have hesn := gen_pow_inj34 (by omega) (by omega) hgs
  subst hesn
  -- the DA roots
  have hd : ∀ d < ed, ∃ (r : List E) (i : ℕ), r.length = 4 ∧ BelowLog (σ (.n 50)) i ∧
      LoadHolds rd (σ (.n 118)) i (base * (gen ^ ex * gen ^ es) * gen ^ d) ∧
      (∀ j < 4, LoadHolds rd (σ (.n 69)) (4 * i + j) (r.getD j 0)) ∧
      ReadsAt rd (cda * gen ^ (4 * d)) r := by
    intro d hd
    obtain ⟨r, hr4, hcall, hreads⟩ := hdas d hd
    obtain ⟨i, hbl, hl, -, hrl⟩ := cover_da_root_sound rd hm _ _ hcall
    refine ⟨r, i, hr4, hbl, hl, hrl, ?_⟩
    rwa [gen_pow_pow] at hreads
  choose! dr di hdrl hdbl hdl' hdrr hdreads using hd
  -- the DA list
  obtain ⟨n, hn, hgn, cellsd, hld, hreadsd, hcand, hdigd⟩ := da_list_digest_sound rd _ _ hdl
  have hn' : n ≤ 16 := hn
  have hedn := gen_pow_inj34 (by omega) (by omega) hgn
  subst hedn
  -- the statement's digest
  obtain ⟨h0, h1, defer, hh0, hh1, hdlen, hdefr, hhdr, hpdig⟩ := statement_digest_sound rd _ _ hsd
  refine ⟨⟨base, sp, cx0, cx1, cs0, cs1, d0, d1, p0, p1, cda, ex, es, ed, ox, cellsx, os, cellss,
    di, dr, cellsd, h0, h1, defer⟩, ?_⟩
  refine ⟨?_, ?_, ⟨hex, hes, hed⟩, hlx, hcanx, ?_, hdigx, hls, hcans, ?_, hdigs, hsp0, hsp1, hcan,
    fun d hd => ⟨hdrl d hd, hdbl d hd, hdl' d hd, hdrr d hd, hdreads d hd⟩, hld, hreadsd, hcand,
    hdigd, hh0, hh1, hdlen, ?_, hhdr, hpdig, ?_, ?_, ?_⟩
  · have := loadHolds_gen_pow_iff.mp hb; simpa using this
  · have := loadHolds_gen_pow_iff.mp hnext; exact this
  · intro j hj
    obtain ⟨h1', h2', h3'⟩ := hrecx j hj
    exact ⟨h1', h2', h3'⟩
  · intro j hj
    obtain ⟨h1', h2', h3'⟩ := hrecs j hj
    exact ⟨h1', h2', h3'⟩
  · rwa [gen_pow_pow] at hdefr
  · rw [gen_pow_pow] at hp0
    have := loadHolds_gen_pow_iff.mp hp0
    simpa using this
  · rw [gen_pow_pow] at hp1
    exact loadHolds_gen_pow_iff.mp hp1
  · rwa [gen_pow_pow] at hsub

end
end LeanVM.Guest.B1.Main
