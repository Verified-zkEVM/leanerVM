/-
  LeanVM.E2E.Complete.DecodeStmtTree

  The words `kidStmt_honest` asks of the honest memory, from `main`'s tree form: the iterations'
  callees' loads, read back by the honest memory, their words `main`'s layout's.
-/

module

public import LeanVM.E2E.Complete.DecodeStmt
public import LeanVM.E2E.Complete.DecodeFrame
public import LeanVM.E2E.Complete.DecodeVsArgs
public import LeanVM.Guest.EndCompleteCTI
public import LeanVM.Guest.B1.Comp.Digest.ChildListLoads
public import LeanVM.Guest.B1.Comp.Digest.SmallLoads

/-!
# Each child's statement, from the trees (D2)

A load equation of the honest tree's `T0` holds on the honest memory (`honest_read_loadEqns`) and
on the memory `rd0` of `main`'s layouts (`T0` is valid there, `loadEqns_read_of_validB`), which
holds `main`'s own `HeapBuf`s (`mainIn`, `mainBuf_read`). So a word a callee's tree loads is, on the
honest memory, the honest table's word at its address:

* `childLoads_tables`: the child-claim digest's blocks (`ChildLoads`, at its precondition
  `CclPreAtC` on `rd0`) give, for each of the child's claims, a slot of the coverage table holding
  its mark and the claim table's entry there, both on the honest memory;
* `loadEqns_kid`, `loop5Q_nodes`: the iterations' nodes and their callees' trees are subtrees of
  `T0`, their load equations `T0`'s;
* `child_words`, `child_words_of_mainQ`: child `c`'s claims (by the child-claim digests, `CclQP`,
  and the DA roots' loop, `Loop100Q`), deferred cells (by the statement digest, `SdQP`) and running
  counts (the iteration's own loads), on the honest memory, at `main`'s buffer pointers;
* `cover_image`: the coverage table's cells on the honest memory are the honest table's or `0`
  (`honest_of_mainCT'`'s image clause: `main`'s `HeapBuf` is no instance's frame);
* `main_bufs_eq`: `main`'s `HeapBuf` sizes in the honest tree are its words';
* `decode_stmts`: every child's statement as V_I decodes it (`kidStmt`) is the witness's, by
  `kidStmt_honest` with the frame's words `mainFrame_words` and counts `countOf_honest`.
-/
namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Main (MainWords mainIn mainLb mainBase mainPtr Loop5Q)
open LeanVM.Guest.B1 (ReadsAt LoadsAt LoadsCells)

@[expose] public section

/-! ## `main`'s tables on `rd0` -/

/-- **`main`'s buffer `i` on a memory holding `main`'s layout.** -/
theorem mainBuf_read {fs : String → ℕ} {fp : ℕ} {W : MainWords} {rd : Reader}
    (h : B1.Main.MemL rd (mainIn fs fp W)) {i : ℕ} (hi : i < 10) {xs : List E}
    (hxs : W.bufs[i]? = some xs) {k : ℕ} (hk : k < xs.length) :
    rd (Parameters.gpow (mainBase fs fp W i + k)) = some xs[k] := by
  have hb : (bases (fp + fs "main") W.sizes)[i]? = some (mainBase fs fp W i) := by
    have hl : i < W.sizes.length := by simp [MainWords.sizes]; omega
    unfold mainBase
    rw [List.getD_eq_getElem?_getD, getElem?_bases hl]
    rfl
  have hq : (mainBase fs fp W i, xs) ∈ mainIn fs fp W := by
    refine List.mem_append_left _ ?_
    unfold mainLb LeanVM.Guest.B1.bufL
    exact List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_zip_eq_some]; exact ⟨hb, hxs⟩⟩
  have := (h _ hq k hk).2
  rwa [B1.Main.addr_ofK] at this

/-- A pointer to `main`'s buffer, shifted. -/
theorem mainPtr_addr {fs : String → ℕ} {fp : ℕ} {W : MainWords} (i a k : ℕ) :
    (mainPtr fs fp W i * gen ^ a).limb 0 * Parameters.gpow k = Parameters.gpow (mainBase fs fp W i + a + k) := by
  rw [mainPtr, B1.Main.ofK_gpow_mul_gen, B1.Main.addr_ofK]

/-! ## The child-claim digest's blocks -/

/-- **The blocks a child-claim digest loads, on the honest memory**: for each of the child's
claims `j < n`, a slot `s' < Lt` of the coverage table, from `o`, holding the mark `g^(mb + j)`,
the claim table (buffer `ie`, `tab`) holding there the claim's entry. -/
theorem childLoads_tables {fs : String → ℕ} {W : MainWords} {rd0 rdL : Reader} {t : Tree}
    (hmem : B1.Main.MemL rd0 (mainIn fs 0 W))
    (hld : ∀ q ∈ t.loadEqns coreProgram, rdL q.1 = some q.2 ∧ rd0 q.1 = some q.2)
    {ie : ℕ} (hie : ie < 10) {tab : List E} (htab : W.bufs[ie]? = some tab)
    {o Lt mb n : ℕ} (hcov : o + Lt ≤ W.cov.length) (htl : 4 * Lt ≤ tab.length) (hLt : Lt < 2 ^ 33)
    (hn : n < 2 ^ 16)
    {Ha : List UInt8 → Option Digest} {off : ℕ → ℕ} {cs rets : List E}
    {marks origin limit ng gsq : E} (hm : marks = gen ^ mb) (ho : origin = gen ^ o)
    (hl : limit = gen ^ Lt) (hng : ng = gen ^ n)
    (hcl : B1.Digest.ChildLoads t (mainPtr fs 0 W ie) (mainPtr fs 0 W 4) marks origin off cs
      (cs.length / 4))
    (hpre : B1.Digest.CclPreAtC Ha off cs rd0 [mainPtr fs 0 W ie, mainPtr fs 0 W 4, marks, origin,
      limit, ng, gsq] rets) :
    ∀ j < n, ∃ s' < Lt, W.cov[o + s']? = some (gen ^ (mb + j)) ∧
      LoadHolds rdL (mainPtr fs 0 W 4) (o + s') (gen ^ (mb + j)) ∧
      ReadsAt rdL (mainPtr fs 0 W ie * gen ^ (4 * s')) ((tab.drop (4 * s')).take 4) := by
  subst hm ho hl hng
  intro j hj
  obtain ⟨-, -, -, -, -, -, -, d0, d1, -, rfl⟩ := B1.Digest.cclPreAtC_shape hpre
  obtain ⟨-, -, n', hn', hng, hcs, hR, -⟩ := hpre
  have hnn : n = n' := B1.Main.gen_pow_inj' (by omega) (by omega) hng
  subst hnn
  have hc4 : cs.length / 4 = n := by omega
  obtain ⟨⟨L, hL, hlim, hoff⟩, hmark, hent⟩ := hR j hj
  have hLL : L = Lt := B1.Main.gen_pow_inj' (by omega) (by omega) hlim.symm
  subst hLL
  have hcl' := hcl j (by omega)
  obtain ⟨hm, hc⟩ := hcl'
  have hmA : (mainPtr fs 0 W 4 * (gen ^ o * gen ^ off j)).limb 0 * Parameters.gpow 0 =
      Parameters.gpow (mainBase fs 0 W 4 + (o + off j)) := by
    rw [← pow_add, mainPtr_addr, Nat.add_zero]
  refine ⟨off j, hoff, ?_, ?_, ?_⟩
  · -- the mark: `rd0`'s word there, the table's
    have h1 := hmark.2
    rw [hmA] at h1
    have h2 := mainBuf_read hmem (i := 4) (by norm_num) (xs := W.cov) rfl (k := o + off j) (by omega)
    rw [h1, ← pow_add] at h2
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq]
    exact (Option.some.inj h2).symm
  · refine ⟨Value.ofK_isInK _, ?_⟩
    have := (hld _ hm).1
    rw [hmA, ← pow_add] at this
    rwa [mainPtr, B1.Main.addr_ofK]
  · intro k hk
    have hk4 : k < 4 := by simp at hk; omega
    have hcs4 : 4 * j + k < cs.length := by omega
    have hcv := hc k (by simp; omega)
    have hev := (hld _ hcv)
    have hent' := hent k (by simp; omega)
    have hA : (mainPtr fs 0 W ie * gen ^ (4 * off j)).limb 0 * Parameters.gpow k =
        Parameters.gpow (mainBase fs 0 W ie + 4 * off j + k) := mainPtr_addr _ _ _
    rw [hA] at hev
    have ht := mainBuf_read hmem hie htab (k := 4 * off j + k) (by omega)
    rw [← Nat.add_assoc] at ht
    have e1 : tab[4 * off j + k] = [cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0,
        cs.getD (4 * j + 3) 0][k] := Option.some.inj (ht.symm.trans hev.2)
    refine ⟨B1.isInK_mul (Value.ofK_isInK _) (B1.gen_pow_isInK _), ?_⟩
    rw [hA, hev.1, ← e1]
    simp [List.getElem_take, List.getElem_drop]

/-! ## Subtrees' load equations -/

theorem mem_loadEqnsKids {P : Core.Program} :
    ∀ {ks : List Tree} {k : Tree}, k ∈ ks → ∀ q ∈ k.loadEqns P, q ∈ Tree.loadEqnsKids P ks
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | k' :: ks, k, h, q, hq => by
      rw [Tree.loadEqnsKids, List.mem_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hq
      · exact Or.inr (mem_loadEqnsKids h q hq)

/-- A callee's load equations are its caller's. -/
theorem loadEqns_kid {P : Core.Program} {f : String} {σ : Val} {bufs : List ℕ} {ks : List Tree}
    {k : Tree} {i : ℕ} (h : ks[i]? = some k) :
    ∀ q ∈ k.loadEqns P, q ∈ (Memory.Tree.node f σ bufs ks).loadEqns P := fun q hq => by
  rw [Tree.loadEqns]
  exact List.mem_append_right _ (mem_loadEqnsKids (List.mem_of_getElem? h) q hq)

/-- **`Loop5Q`'s iterations are subtrees**: iteration `c`'s node, with `Loop5H` at child `j + c`,
its load equations the tree's. -/
theorem loop5Q_nodes {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop}
    {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC}
    {CQ SQ : List E → List E → ℕ → Reader → Tree → Prop} {LQ : List E → ℕ → Reader → Tree → Prop}
    {IQ : ℕ → Reader → Val → Prop} {fs : String → ℕ} {rd : Reader} :
    ∀ (n j fp : ℕ) (t : Tree), Loop5Q VsQ vr CQ SQ LQ IQ fs n j fp rd t → ∀ c < n,
      ∃ (fp' : ℕ) (σ : Val) (bufs : List ℕ) (ks : List Tree) (k : Tree),
        (∀ q ∈ (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).loadEqns coreProgram,
          q ∈ t.loadEqns coreProgram) ∧
        Loop5H VsQ vr CQ SQ LQ IQ fs (j + c) fp' rd σ bufs ks k
  | 0, _, _, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | n + 1, j, fp, t, hQ, c, hc => by
      obtain ⟨σ, bufs, ks, k, rfl, hIQ, h0, h1, h2, h4, hv, hrest⟩ := hQ
      rcases c with _ | c
      · exact ⟨fp, σ, bufs, ks, k, fun q hq => hq, hIQ, h0, h1, h2, h4, hv⟩
      · obtain ⟨fp', σ', bufs', ks', k', hsub, hH⟩ :=
          loop5Q_nodes n (j + 1) (fp + fs "__loop5") k hrest c (by omega)
        refine ⟨fp', σ', bufs', ks', k', fun q hq =>
          loadEqns_kid (by simp : (ks ++ [k])[ks.length]? = some k) q (hsub q hq), ?_⟩
        rw [show j + (c + 1) = j + 1 + c by omega]
        exact hH


/-! ## An iteration's words -/

/-- The iteration's words at its callees' calls and its running-count loads. -/
theorem loop5ValC_kidWords (rd : Reader) (N written lxT cover lxS gsq spT spS carried daR daC daS
    seed0 seed1 cpi glp cfresh : E) (c : ℕ) (r : B1.Main.ChildWords) (sigp cda : E) (dd : Digest) :
    ([.n 3, .n 4, .n 19, .n 31, .n 5, .n 20, .n 6] : List V).map (B1.Main.loop5ValC rd N written lxT
      cover lxS gsq spT spS carried daR daC daS seed0 seed1 cpi glp cfresh c r sigp cda dd) =
      [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq] ∧
    ([.n 7, .n 4, .n 34, .n 5, .n 8, .n 21, .n 6] : List V).map (B1.Main.loop5ValC rd N written lxT
      cover lxS gsq spT spS carried daR daC daS seed0 seed1 cpi glp cfresh c r sigp cda dd) =
      [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq] ∧
    ([.n 62, .n 52, .n 59, .n 10, .n 11, .n 12, .n 19, .n 30] : List V).map (B1.Main.loop5ValC rd N
      written lxT cover lxS gsq spT spS carried daR daC daS seed0 seed1 cpi glp cfresh c r sigp cda dd) =
      [1, gen ^ r.da.length, cda, daR, daC, daS, r.base, gen ^ r.nx * gen ^ r.ns] ∧
    ([.n 13, .n 14, .n 42, .n 63, .n 64, .n 51] : List V).map (B1.Main.loop5ValC rd N written lxT
      cover lxS gsq spT spS carried daR daC daS seed0 seed1 cpi glp cfresh c r sigp cda dd) =
      [seed0, seed1, sigp, (Blake2sHash.digestScalars dd).1, (Blake2sHash.digestScalars dd).2,
        carried * gen ^ (53 * c)] ∧
    ([.n 61, .n 18, .n 19, .n 82, .n 81] : List V).map (B1.Main.loop5ValC rd N written lxT
      cover lxS gsq spT spS carried daR daC daS seed0 seed1 cpi glp cfresh c r sigp cda dd) =
      [1 + gen ^ r.da.length, written * gen ^ c, r.base, written * gen ^ c,
        r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.da.length] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.map_cons, List.map_nil, B1.Main.loop5ValC] <;> b1_look

set_option maxRecDepth 100000 in
theorem loop5_count_loads : (.n 19, .n 18, 0) ∈ loadsOf B1.Main.loop5Pre ∧
    (.n 81, .n 82, 1) ∈ loadsOf B1.Main.loop5Pre := by
  constructor <;> decide +kernel

/-- **The iteration's running-count loads are load equations of its node.** -/
theorem loop5_count_eqns {σ : Val} {bufs : List ℕ} {ks : List Tree} :
    ((σ (.n 18)).limb 0 * Parameters.gpow 0, σ (.n 19)) ∈
        (Memory.Tree.node "__loop5" σ bufs ks).loadEqns coreProgram ∧
      ((σ (.n 82)).limb 0 * Parameters.gpow 1, σ (.n 81)) ∈
        (Memory.Tree.node "__loop5" σ bufs ks).loadEqns coreProgram := by
  have hw : walk σ (Fn.body Data.core35) = .ret (B1.Main.loop5Pre.flatMap (slEvs σ)) [] := by
    rw [B1.Main.core35_split]
    exact walk_straight σ [] _ B1.Main.loop5_parts.1
  have hev := events_node (P := coreProgram) (bufs := bufs) (kids := ks) B1.Main.find_loop5 hw
  have hl : ∀ {d p : V} {o : ℕ}, (d, p, o) ∈ loadsOf B1.Main.loop5Pre →
      ((σ p).limb 0 * Parameters.gpow o, σ d) ∈ (Memory.Tree.node "__loop5" σ bufs ks).loadEqns coreProgram := by
    intro d p o h
    rw [Tree.loadEqns, hev]
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨.atom (.load d p o), ?_, ?_⟩)
    · exact List.mem_flatMap.mpr ⟨_, mem_of_loadsOf h, by simp [slEvs]⟩
    · simp [atomLoadEqns]
  exact ⟨hl loop5_count_loads.1, hl loop5_count_loads.2⟩


/-! ## A child's words, from its iteration -/

/-- The child-claim digests' predicate with its precondition on the reader. -/
def CclQP (Ha : List UInt8 → Option Digest) : List E → List E → ℕ → Reader → Tree → Prop :=
  fun args rets b rd t => ∃ off cs, B1.Digest.CclLoadsQ off cs args rets b rd t ∧
    B1.Digest.CclPreAtC Ha off cs rd args rets

/-- The statement digest's predicate with its precondition on the reader. -/
def SdQP (Ha : List UInt8 → Option Digest) : List E → List E → ℕ → Reader → Tree → Prop :=
  fun args rets b rd t => ∃ sig cells, B1.Digest.SdLoadsQ sig cells args rets b rd t ∧
    B1.Digest.SdPreAtC Ha sig cells rd args rets

theorem length_flatMap_four {α : Type} (f : α → List E) (hf : ∀ a, (f a).length = 4) :
    ∀ l : List α, (l.flatMap f).length = 4 * l.length
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, List.length_append, hf, length_flatMap_four f hf l, List.length_cons]
      ring

/-- A table read through `main`'s buffer pointer: the honest memory reads `xs` at `p·g^a`, word by
word, where both memories read the same load equations and `rd0` holds the table. -/
theorem readsAt_table {fs : String → ℕ} {W : MainWords} {rd0 rdL : Reader}
    (hmem : B1.Main.MemL rd0 (mainIn fs 0 W)) {i : ℕ} (hi : i < 10) {tab : List E}
    (htab : W.bufs[i]? = some tab) {a : ℕ} {xs : List E} (hlen : a + xs.length ≤ tab.length)
    (hrd : ∀ k < xs.length, ∃ v, rdL (Parameters.gpow (mainBase fs 0 W i + a + k)) = some v ∧
      rd0 (Parameters.gpow (mainBase fs 0 W i + a + k)) = some v) :
    ReadsAt rdL (mainPtr fs 0 W i * gen ^ a) ((tab.drop a).take xs.length) := by
  intro k hk
  simp only [List.length_take, List.length_drop] at hk
  have hk' : k < xs.length := by omega
  obtain ⟨v, h1, h2⟩ := hrd k hk'
  have ht := mainBuf_read hmem hi htab (k := a + k) (by omega)
  rw [← Nat.add_assoc, h2] at ht
  refine ⟨B1.isInK_mul (Value.ofK_isInK _) (B1.gen_pow_isInK _), ?_⟩
  rw [mainPtr_addr, h1, Option.some.inj ht]
  simp [List.getElem_take, List.getElem_drop]


set_option maxHeartbeats 1000000 in
/-- **Child `c`'s words on the honest memory, from its iteration**: the iteration's callees' trees
(the child-claim digests', the DA roots' loop's, the statement digest's) and its running-count
loads give `kidStmt_honest`'s memory facts at `main`'s buffer pointers. -/
theorem child_words {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} {rd0 rdL : Reader}
    (hmem : B1.Main.MemL rd0 (mainIn B2C.fs 0 (B1.Main.honestWordsC Ht seed s w)))
    {c : ℕ} (hc : c < w.children.length)
    (hB : s.claims.xmss.length + (B1.Main.planX s w).2.length +
      (s.claims.sphincs.length + (B1.Main.planS s w).2.length) +
      (s.claims.da.length + (B1.Main.planD s w).2.length) < 2 ^ 16)
    (hcx : w.children[c].statement.claims.xmss.length < 2 ^ 16)
    (hcs : w.children[c].statement.claims.sphincs.length < 2 ^ 16)
    (hcd : w.children[c].statement.claims.da.length ≤ 16)
    (hdl : ∀ c' ∈ w.children, c'.statement.defer.cells.length = 53)
    {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop}
    {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC} {fp' : ℕ} {σ : Val} {bufs : List ℕ}
    {ks : List Tree} {k : Tree}
    (hH : Loop5H VsQ vr (CclQP Ha) (SdQP Ha) B1.Main.Loop100Q
      (B1.Main.mainIQ B2C.fs 0 (B1.Main.honestWordsC Ht seed s w)) B2C.fs c fp' rd0 σ bufs ks k)
    (hld : ∀ q ∈ (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).loadEqns coreProgram,
      rdL q.1 = some q.2 ∧ rd0 q.1 = some q.2) :
    (∀ j < w.children[c].statement.claims.xmss.length,
      ∃ s' < s.claims.xmss.length + (B1.Main.planX s w).2.length,
        (B1.Main.honestWordsC Ht seed s w).cov[s']? = some (gen ^ (B1.Main.hbase s w c + j)) ∧
        LoadHolds rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 4) s'
          (gen ^ (B1.Main.hbase s w c + j)) ∧
        ReadsAt rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 1 * gen ^ (4 * s'))
          (((B1.Main.honestWordsC Ht seed s w).xTab.drop (4 * s')).take 4)) ∧
    (∀ j < w.children[c].statement.claims.sphincs.length,
      ∃ s' < s.claims.sphincs.length + (B1.Main.planS s w).2.length,
        (B1.Main.honestWordsC Ht seed s w).cov[s.claims.xmss.length + (B1.Main.planX s w).2.length + s']? =
          some (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        LoadHolds rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 4)
          (s.claims.xmss.length + (B1.Main.planX s w).2.length + s')
          (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        ReadsAt rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 2 * gen ^ (4 * s'))
          (((B1.Main.honestWordsC Ht seed s w).sTab.drop (4 * s')).take 4)) ∧
    (∀ j < w.children[c].statement.claims.da.length,
      ∃ i < s.claims.da.length + (B1.Main.planD s w).2.length,
        (B1.Main.honestWordsC Ht seed s w).cov[s.claims.xmss.length + (B1.Main.planX s w).2.length +
          (s.claims.sphincs.length + (B1.Main.planS s w).2.length) + i]? =
          some (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length +
            w.children[c].statement.claims.sphincs.length + j))) ∧
        LoadHolds rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 4 *
            gen ^ (s.claims.xmss.length + (B1.Main.planX s w).2.length +
              (s.claims.sphincs.length + (B1.Main.planS s w).2.length))) i
          (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length +
            w.children[c].statement.claims.sphincs.length + j))) ∧
        ReadsAt rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 0 * gen ^ (4 * i))
          (((B1.Main.honestWordsC Ht seed s w).daTab.drop (4 * i)).take 4)) ∧
    ReadsAt rdL (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 7 * gen ^ (53 * c))
      w.children[c].statement.defer.cells ∧
    rdL ((mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 8).limb 0 * Parameters.gpow c) =
      some (gen ^ B1.Main.hbase s w c) ∧
    rdL ((mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 8).limb 0 * Parameters.gpow (c + 1)) =
      some (gen ^ B1.Main.hbase s w (c + 1)) := by
  set W := B1.Main.honestWordsC Ht seed s w with hW
  set st := w.children[c].statement with hst
  have hr : W.child c = B1.Main.childWordsOfC Ht seed w.children[c] (B1.Main.hbase s w c) := by
    simp only [hW, B1.Main.honestWordsC, hc, ↓reduceDIte]
  obtain ⟨⟨b, dd, hσ⟩, ⟨kc0, bc0, hk0, -, off0, cs0, hcl0, hpre0⟩,
    ⟨kc1, bc1, hk1, -, off1, cs1, hcl1, hpre1⟩, h2, ⟨kd, bd, hk4, -, sig, cells, hsd, hsdp⟩, -⟩ := hH
  subst hσ
  obtain ⟨a0, a1, a2, a4, a5⟩ := loop5ValC_kidWords rd0 (gen ^ W.nc)
    (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 8))) (mainPtr B2C.fs 0 W 1) (mainPtr B2C.fs 0 W 4)
    (gen ^ W.dx * gen ^ W.ux) (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W + 34)))
    (mainPtr B2C.fs 0 W 2) (gen ^ W.ds * gen ^ W.us) (mainPtr B2C.fs 0 W 7) (mainPtr B2C.fs 0 W 0)
    (mainPtr B2C.fs 0 W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)))
    (gen ^ W.da * gen ^ W.ud) (Blake2sHash.digestScalars W.seed).1 (Blake2sHash.digestScalars W.seed).2
    (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 5))) (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W)))
    (mainPtr B2C.fs 0 W 6) c (W.child c) (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 2))) dd
  rw [a0] at hcl0 hpre0
  rw [a1] at hcl1 hpre1
  rw [a4] at hsd hsdp
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at a5
  obtain ⟨e61, e18, e19, e82, e81, -⟩ := a5
  have hbase : (W.child c).base = gen ^ B1.Main.hbase s w c := by rw [hr]; rfl
  have hnx : (W.child c).nx = st.claims.xmss.length := by rw [hr]; rfl
  have hns : (W.child c).ns = st.claims.sphincs.length := by rw [hr]; rfl
  have hnd : (W.child c).da = st.claims.da := by rw [hr]; rfl
  have hndl : (W.child c).da.length = st.claims.da.length := by rw [hnd]
  have hdx : W.dx = s.claims.xmss.length := rfl
  have hux : W.ux = (B1.Main.planX s w).2.length := rfl
  have hds : W.ds = s.claims.sphincs.length := rfl
  have hus : W.us = (B1.Main.planS s w).2.length := rfl
  have hda : W.da = s.claims.da.length := rfl
  have hud : W.ud = (B1.Main.planD s w).2.length := rfl
  have hcl : W.cov.length = W.dx + W.ux + (W.ds + W.us) + (W.da + W.ud) :=
    B1.Main.honestWordsC_cov_length Ht seed
  have hxl : W.xTab.length = 4 * (W.dx + W.ux) := by
    show ((s.claims.xmss ++ (B1.Main.planX s w).2).flatMap B1.Main.xCellsOf).length = _
    rw [length_flatMap_four _ (fun _ => by simp [B1.Main.xCellsOf])]; simp; rfl
  have hsl : W.sTab.length = 4 * (W.ds + W.us) := by
    show ((s.claims.sphincs ++ (B1.Main.planS s w).2).flatMap B1.Main.sCellsOf).length = _
    rw [length_flatMap_four _ (fun _ => by simp [B1.Main.sCellsOf])]; simp; rfl
  have hdlen : W.daTab.length = 4 * (W.da + W.ud) := by
    show ((s.claims.da ++ (B1.Main.planD s w).2).flatMap B1.Main.daCellsOf).length = _
    rw [length_flatMap_four _ (fun _ => rfl)]; simp; rfl
  have hldk : ∀ {i : ℕ} {kk : Tree}, ks[i]? = some kk → ∀ q ∈ kk.loadEqns coreProgram,
      rdL q.1 = some q.2 ∧ rd0 q.1 = some q.2 := by
    intro i kk h q hq
    have h' : (ks ++ [k])[i]? = some kk := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h
    exact hld q (loadEqns_kid h' q hq)
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
  · -- the leanXMSS claims
    obtain ⟨s', hs', h1, h2, h3⟩ := childLoads_tables hmem (hldk hk0) (ie := 1) (by norm_num) rfl
      (o := 0) (Lt := W.dx + W.ux) (by omega) (by omega) (by omega) hcx hbase (pow_zero gen).symm
      (pow_add gen _ _).symm (by rw [hnx]) hcl0 hpre0 j hj
    rw [Nat.zero_add] at h1 h2
    exact ⟨s', hs', h1, h2, h3⟩
  · -- the leanSPHINCS claims
    obtain ⟨s', hs', h1, h2, h3⟩ := childLoads_tables hmem (hldk hk1) (ie := 2) (by norm_num) rfl
      (o := W.dx + W.ux) (Lt := W.ds + W.us) (mb := B1.Main.hbase s w c + st.claims.xmss.length)
      (by omega) (by omega) (by omega) hcs (by rw [hbase, hnx, pow_add]) (pow_add gen _ _).symm
      (pow_add gen _ _).symm (by rw [hns]) hcl1 hpre1 j hj
    rw [show B1.Main.hbase s w c + st.claims.xmss.length + j =
      B1.Main.hbase s w c + (st.claims.xmss.length + j) by omega] at h1 h2
    exact ⟨s', hs', h1, h2, h3⟩
  · -- the DA claims, from the DA roots' loop
    have hj' : j < (W.child c).da.length := by rw [hnd]; exact hj
    have h61 : B1.Main.loop5ValC rd0 (gen ^ W.nc)
        (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 8))) (mainPtr B2C.fs 0 W 1) (mainPtr B2C.fs 0 W 4)
        (gen ^ W.dx * gen ^ W.ux) (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W + 34)))
        (mainPtr B2C.fs 0 W 2) (gen ^ W.ds * gen ^ W.us) (mainPtr B2C.fs 0 W 7) (mainPtr B2C.fs 0 W 0)
        (mainPtr B2C.fs 0 W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)))
        (gen ^ W.da * gen ^ W.ud) (Blake2sHash.digestScalars W.seed).1 (Blake2sHash.digestScalars W.seed).2
        (ofK (Parameters.gpow (B1.Main.mainBase B2C.fs 0 W 5)))
        (ofK (Parameters.gpow (B1.Main.mainExpBase B2C.fs 0 W)))
        (mainPtr B2C.fs 0 W 6) c (W.child c) (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 2))) dd
        (.n 61) ≠ 0 := by
      rw [e61]
      exact of_decide_eq_true (by
        rw [B1.Main.one_add_gen_pow_decide (by rw [hnd]; exact hcd)]; exact decide_eq_true (by omega))
    obtain ⟨kl, bl, hk2, -, hLQ⟩ := h2 h61
    rw [a2] at hLQ
    obtain ⟨m, sl, rt, hm16, hm, ⟨M, hM16, hM, hslM⟩, hA⟩ := hLQ
    have hmm : m = (W.child c).da.length := B1.Main.gen_pow_inj' (by omega) (by omega) hm.symm
    subst hmm
    have hMM : M = W.da + W.ud := by
      rw [← pow_add] at hM
      exact (B1.Main.gen_pow_inj' (by omega) (by omega) hM).symm
    subst hMM
    have hi := hslM j hj'
    have hX : gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us) = gen ^ (W.dx + W.ux + (W.ds + W.us)) := by
      simp only [← pow_add]
    have q1 := hldk hk2 _ (hA _ ⟨j, Nat.zero_le _, hj', Or.inl rfl⟩)
    have hmk : (W.child c).base * (gen ^ (W.child c).nx * gen ^ (W.child c).ns) * gen ^ j =
        gen ^ (B1.Main.hbase s w c + (st.claims.xmss.length + st.claims.sphincs.length + j)) := by
      rw [hbase, hnx, hns, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
    rw [hX, mul_assoc, ← pow_add, mainPtr_addr, hmk] at q1
    have hcv := mainBuf_read hmem (i := 4) (by norm_num) (xs := W.cov) rfl
      (k := W.dx + W.ux + (W.ds + W.us) + sl j) (by omega)
    rw [Nat.add_zero] at q1
    rw [q1.2] at hcv
    refine ⟨sl j, hi, ?_, ⟨B1.isInK_mul (Value.ofK_isInK _) (B1.gen_pow_isInK _), ?_⟩, ?_⟩
    · rw [List.getElem?_eq_getElem (by omega), Option.some.injEq]
      exact (Option.some.inj hcv).symm
    · rw [mainPtr_addr, Nat.add_assoc]; exact q1.1
    · refine readsAt_table hmem (i := 0) (by norm_num) (tab := W.daTab) rfl (a := 4 * sl j)
        (xs := [0, 0, 0, 0]) (by simp; omega) fun kk hkk => ?_
      have q2 := hldk hk2 _ (hA _ ⟨j, Nat.zero_le _, hj', Or.inr ⟨kk, by simpa using hkk, rfl⟩⟩)
      rw [mainPtr_addr] at q2
      exact ⟨_, q2.1, q2.2⟩
  · -- the deferred cells, from the statement digest
    simp only [List.map_cons, List.map_nil] at hsd hsdp
    obtain ⟨-, -, hcells⟩ := hsd
    obtain ⟨-, -, hlen, -, -, -, -, hc0, -⟩ := hsdp
    have h53 : st.claims.da.length = st.claims.da.length := rfl
    have hst53 : st.defer.cells.length = 53 := hdl _ (List.getElem_mem hc)
    intro kk hkk
    have hkk53 : kk < 53 := by omega
    have hkc : kk < cells.length := by rw [hlen]; exact hkk53
    have r0 := (hc0 kk hkc).2
    have rL := (hldk hk4 _ (hcells kk hkc)).1
    rw [mainPtr_addr] at r0 rL
    have hflat := B1.Main.getElem_flatten_uniform (w := 53) (w.children.map fun c => c.statement.defer.cells)
      (fun x hx => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; exact hdl a ha) c (by simpa using hc)
      kk hkk53
    obtain ⟨hfl, hfe⟩ := hflat
    have hct : W.carTab = (w.children.map fun c => c.statement.defer.cells).flatten := by
      rfl
    have hcv := mainBuf_read hmem (i := 7) (by norm_num) (xs := W.carTab) rfl (k := 53 * c + kk)
      (by rw [hct]; exact hfl)
    rw [← Nat.add_assoc, r0] at hcv
    have e : cells[kk] = st.defer.cells[kk] := by
      have := Option.some.inj hcv
      rw [this]
      simp only [hct, hfe]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, hst]
      rw [List.getElem?_eq_getElem hkk]; rfl
    refine ⟨B1.isInK_mul (Value.ofK_isInK _) (B1.gen_pow_isInK _), ?_⟩
    rw [mainPtr_addr, rL, e]
  · -- the running count at child `c`
    have := (hld _ (loop5_count_eqns (bufs := bufs) (ks := ks ++ [k])).1).1
    rw [e18, e19, hbase, B1.Main.ofK_gpow_mul_gen, B1.Main.addr_ofK, Nat.add_zero] at this
    rw [mainPtr, B1.Main.addr_ofK]
    exact this
  · -- the running count after child `c`
    have := (hld _ (loop5_count_eqns (bufs := bufs) (ks := ks ++ [k])).2).1
    rw [e82, e81, hbase, hnx, hns, hnd, B1.Main.ofK_gpow_mul_gen, B1.Main.addr_ofK] at this
    rw [mainPtr, B1.Main.addr_ofK, (B1.Main.honest_child_slots Ht seed hc).1]
    rw [← pow_add, ← pow_add, ← pow_add] at this
    rw [show B1.Main.hbase s w c + (st.claims.xmss.length + st.claims.sphincs.length +
      st.claims.da.length) = B1.Main.hbase s w c + (st.claims.xmss.length + st.claims.sphincs.length) +
      st.claims.da.length by omega]
    exact this


/-! ## The coverage table on the honest memory -/

/-- **Every coverage cell of the honest memory is the honest table's or `0`**: a word of the honest
memory is `0`, `rd0`'s (the layouts', holding `main`'s tables) or a frame's, and `main`'s
coverage buffer, its own `HeapBuf`, is no instance's frame. -/
theorem cover_image {fs : String → ℕ} {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)}
    {hdr : E × E} {T0 : Tree} {ν : ℕ → String → Val → V → E} {rd0 : Reader} {W : MainWords}
    {σ0 : Val} {ks : List Tree} (hT0 : T0 = .node "main" σ0 W.sizes ks)
    (htot : T0.total fs < 2 ^ 32) (hmem : B1.Main.MemL rd0 (mainIn fs 0 W))
    (himg : ∀ (a : K) (x : E), (honest coreProgram fs H C hdr (T0.retemp coreProgram fs ν 0)).read a =
        some x → x = 0 ∨ rd0 a = some x ∨
          ∃ I ∈ honestInsts coreProgram fs H hdr T0, ∃ i, I.Frame fs i ∧ a = Parameters.gpow i)
    (hcl : W.cov.length = W.total) :
    ∀ s' < W.cov.length,
      B1.Main.cellAt (honest coreProgram fs H C hdr (T0.retemp coreProgram fs ν 0)).read
          (mainPtr fs 0 W 4) s' = 0 ∨
        W.cov[s']? = some (B1.Main.cellAt (honest coreProgram fs H C hdr
          (T0.retemp coreProgram fs ν 0)).read (mainPtr fs 0 W 4) s') := by
  intro s' hs'
  unfold B1.Main.cellAt
  rw [mainPtr, B1.Main.addr_ofK]
  cases h : (honest coreProgram fs H C hdr (T0.retemp coreProgram fs ν 0)).read
      (Parameters.gpow (mainBase fs 0 W 4 + s')) with
  | none => left; rfl
  | some x =>
    simp only [Option.getD_some]
    rcases himg _ _ h with h0 | h1 | ⟨I, hI, i, hfr, hai⟩
    · exact Or.inl h0
    · right
      have := mainBuf_read hmem (i := 4) (by norm_num) (xs := W.cov) rfl hs'
      rw [List.getElem?_eq_getElem hs']
      rw [h1] at this
      exact congrArg some (Option.some.inj this).symm
    · exfalso
      -- the coverage buffer is the root's fifth `HeapBuf`
      set I0 : Inst := ⟨.node "main" σ0 W.sizes ks, 0, hdr,
        kidPos fs coreProgram.loop 0 "main" W.sizes (ks.map (Tree.total fs)),
        bases (bufBase fs coreProgram.loop 0 "main" (ks.map (Tree.total fs))) W.sizes⟩ with hI0
      have hb0 : I0.Buf (mainBase fs 0 W 4 + s') := by
        have hl : 4 < W.sizes.length := by simp [MainWords.sizes]
        have hbb : bufBase fs coreProgram.loop 0 "main" (ks.map (Tree.total fs)) = 0 + fs "main" := by
          simp [bufBase, B1.Main.main_not_loop]
        refine ⟨(W.sizes[4], mainBase fs 0 W 4), ?_, by simp, ?_⟩
        · simp only [hI0, Tree.bufs, hbb]
          refine List.mem_iff_getElem?.mpr ⟨4, ?_⟩
          rw [List.getElem?_zip_eq_some]
          refine ⟨List.getElem?_eq_getElem hl, ?_⟩
          unfold mainBase
          simp [List.getD_eq_getElem?_getD, getElem?_bases hl]
        · have : W.sizes[4] = W.total := rfl
          simp only [this]; omega
      have hins : honestInsts coreProgram fs H hdr T0 = I0 :: Tree.instsKids fs coreProgram.loop H I0 0
          (kidPos fs coreProgram.loop 0 "main" W.sizes (ks.map (Tree.total fs))) ks := by
        rw [honestInsts, hT0, insts_node]
      have hpw := insts_pairwise (fs := fs) (lp := coreProgram.loop) (H := H) T0 0 hdr
      have hwi := insts_within (fs := fs) (lp := coreProgram.loop) (H := H) T0 0 hdr
      rw [← honestInsts] at hpw hwi
      rw [hins] at hpw hwi hI
      have hiw := hwi I hI i (Or.inl hfr)
      have hbw := hwi I0 List.mem_cons_self _ (Or.inr hb0)
      have hii : i = mainBase fs 0 W 4 + s' := by
        have := Parameters.gpow_injOn (show i ∈ Set.Iio (2 ^ 64 - 1) by simp; omega)
          (show mainBase fs 0 W 4 + s' ∈ Set.Iio (2 ^ 64 - 1) by simp; omega) hai.symm
        exact this
      subst hii
      rcases List.mem_cons.mp hI with rfl | hI'
      · exact (insts_placed (fs := fs) (lp := coreProgram.loop) (H := H) T0 0 hdr I0
          (by rw [← honestInsts, hins]; exact List.mem_cons_self)).frame_buf hfr hb0
      · exact (List.rel_of_pairwise_cons hpw hI') _ (Or.inr hb0) (Or.inl hfr)


/-- **`main`'s `HeapBuf`s in the honest tree are its words' sizes** (`Tree.BufsOk` of the re-chosen
tree, `mainS_allocs`). -/
theorem main_bufs_eq {S : BlakeSem} {Ha : List UInt8 → Option Digest} {κ : ℕ}
    {VsGood : B1.VerifySub.VsData → B1.VerifySub.VsRunC → Prop} {W : MainWords} {rd0 : Reader}
    (hW : B1.Main.MainWordsOkC S B2C.fs Ha κ VsGood 0 W) {T0 : Tree} {ν : ℕ → String → Val → V → E}
    {σ0 : Val} {bufs : List ℕ} {ks : List Tree} (hT0 : T0 = .node "main" σ0 bufs ks)
    (hσ0 : σ0 = B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 W))
    (hbo : (T0.retemp coreProgram B2C.fs ν 0).BufsOk coreProgram) : bufs = W.sizes := by
  rw [hT0, retemp_node] at hbo
  obtain ⟨hb, -⟩ := hbo
  have hf : coreProgram.find? "main" = some Data.core0 := B1.Main.find_main
  have hw : walk σ0 (Fn.body Data.core0) = .ret (B1.Main.mainEvs σ0) [] := by
    rw [B1.Main.core0_body]; exact B1.Main.walk_mainBody σ0
  rw [events_retemp coreProgram_fresh (bufs' := bufs) (ks' := ks), events_node hf hw,
    allocs_congr (evAgree_retemp coreProgram_fresh hf hw)] at hb
  rw [hb, B1.Main.allocs_mainEvs]
  have hb1 : decide (σ0 (.n 112) = 0) = decide (W.rd = 1) := by rw [hσ0]; exact B1.Main.branch1 hW.rd1
  have hb2 : decide (σ0 (.n 155) = 0) = decide (W.nc = 0) := by rw [hσ0]; exact B1.Main.branch2 hW.nc
  obtain ⟨q1, -, -, -⟩ := B1.Main.mainLin_parts (decide (W.rd = 1)) (decide (W.nc = 0))
  obtain ⟨-, e2, -, -⟩ := straight_parts σ0 _ (B1.Main.mainLin_straight (decide (W.rd = 1))
    (decide (W.nc = 0)))
  rw [q1] at e2
  rw [hb1, hb2, e2, hσ0]
  exact B1.Main.mainS_allocs hW



set_option maxHeartbeats 1000000 in
/-- `child_words` along `main`'s tree form: every child's iteration is a subtree of `T0`. -/
theorem child_words_of_mainQ {S : BlakeSem} {Ha : List UInt8 → Option Digest}
    {Ht : List UInt8 → Digest} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {κ : ℕ}
    {VsGood : B1.VerifySub.VsData → B1.VerifySub.VsRunC → Prop}
    (hW : B1.Main.MainWordsOkC S B2C.fs Ha κ VsGood 0 (B1.Main.honestWordsC Ht seed s w))
    {hdr : E × E} {rd0 : Reader} {T0 : Tree} {ν : ℕ → String → Val → V → E}
    {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop}
    {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC} {σ0 : Val} {ks : List Tree}
    (hT0 : T0 = .node "main" σ0 (B1.Main.honestWordsC Ht seed s w).sizes ks)
    (hnc : w.children.length ≠ 0 → ∃ (i : ℕ) (k : Tree) (b : ℕ), ks[i]? = some k ∧
      (bases (0 + B2C.fs "main" + (B1.Main.honestWordsC Ht seed s w).sizes.sum)
        (ks.map (Tree.total B2C.fs)))[i]? = some b ∧
      Loop5Q VsQ vr (CclQP Ha) (SdQP Ha) B1.Main.Loop100Q
        (B1.Main.mainIQ B2C.fs 0 (B1.Main.honestWordsC Ht seed s w)) B2C.fs w.children.length 0 b rd0 k)
    (hboth : ∀ q ∈ T0.loadEqns coreProgram,
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read q.1 = some q.2 ∧
        rd0 q.1 = some q.2)
    (hmem : B1.Main.MemL rd0 (mainIn B2C.fs 0 (B1.Main.honestWordsC Ht seed s w)))
    (hdl : ∀ c' ∈ w.children, c'.statement.defer.cells.length = 53)
    {c : ℕ} (hc : c < w.children.length) :
    (∀ j < w.children[c].statement.claims.xmss.length,
      ∃ s' < s.claims.xmss.length + (B1.Main.planX s w).2.length,
        (B1.Main.honestWordsC Ht seed s w).cov[s']? = some (gen ^ (B1.Main.hbase s w c + j)) ∧
        LoadHolds (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 4) s'
          (gen ^ (B1.Main.hbase s w c + j)) ∧
        ReadsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 1 * gen ^ (4 * s'))
          (((B1.Main.honestWordsC Ht seed s w).xTab.drop (4 * s')).take 4)) ∧
    (∀ j < w.children[c].statement.claims.sphincs.length,
      ∃ s' < s.claims.sphincs.length + (B1.Main.planS s w).2.length,
        (B1.Main.honestWordsC Ht seed s w).cov[s.claims.xmss.length + (B1.Main.planX s w).2.length + s']? =
          some (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        LoadHolds (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 4)
          (s.claims.xmss.length + (B1.Main.planX s w).2.length + s')
          (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        ReadsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 2 * gen ^ (4 * s'))
          (((B1.Main.honestWordsC Ht seed s w).sTab.drop (4 * s')).take 4)) ∧
    (∀ j < w.children[c].statement.claims.da.length,
      ∃ i < s.claims.da.length + (B1.Main.planD s w).2.length,
        (B1.Main.honestWordsC Ht seed s w).cov[s.claims.xmss.length + (B1.Main.planX s w).2.length +
          (s.claims.sphincs.length + (B1.Main.planS s w).2.length) + i]? =
          some (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length +
            w.children[c].statement.claims.sphincs.length + j))) ∧
        LoadHolds (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 4 *
            gen ^ (s.claims.xmss.length + (B1.Main.planX s w).2.length +
              (s.claims.sphincs.length + (B1.Main.planS s w).2.length))) i
          (gen ^ (B1.Main.hbase s w c + (w.children[c].statement.claims.xmss.length +
            w.children[c].statement.claims.sphincs.length + j))) ∧
        ReadsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 0 * gen ^ (4 * i))
          (((B1.Main.honestWordsC Ht seed s w).daTab.drop (4 * i)).take 4)) ∧
    ReadsAt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read (mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 7 * gen ^ (53 * c))
      w.children[c].statement.defer.cells ∧
    (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read ((mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 8).limb 0 * Parameters.gpow c) =
      some (gen ^ B1.Main.hbase s w c) ∧
    (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read ((mainPtr B2C.fs 0 (B1.Main.honestWordsC Ht seed s w) 8).limb 0 * Parameters.gpow (c + 1)) =
      some (gen ^ B1.Main.hbase s w (c + 1)) := by
  set W := B1.Main.honestWordsC Ht seed s w with hWdef
  obtain ⟨i5, k5, b5, hk5, -, hL5⟩ := hnc (by omega)
  obtain ⟨fp', σ, bufs', ks', k', hsub, hH5⟩ := loop5Q_nodes w.children.length 0 b5 k5 hL5 c hc
  rw [Nat.zero_add] at hH5
  have hok := hW.children c hc
  have hr : W.child c = B1.Main.childWordsOfC Ht seed w.children[c] (B1.Main.hbase s w c) := by
    simp only [hWdef, B1.Main.honestWordsC, hc, ↓reduceDIte]
  have hnx := hok.nx
  have hns := hok.ns
  have hnd := hok.nda
  rw [hr] at hnx hns hnd
  have ht := hW.total
  have e1 : W.total = s.claims.xmss.length + (B1.Main.planX s w).2.length +
      (s.claims.sphincs.length + (B1.Main.planS s w).2.length) +
      (s.claims.da.length + (B1.Main.planD s w).2.length) := rfl
  exact child_words hmem hc (by omega)
    hnx hns hnd hdl hH5 fun q hq => hboth q (by rw [hT0]; exact loadEqns_kid hk5 q (hsub q hq))

/-! ## The children's statements -/

set_option maxHeartbeats 1000000 in
/-- **D2: every child's statement, decoded off the honest memory** (`kidStmt`, as `decKid` reads
it): from `main`'s tree form on the layouts' memory `rd0` (its child-claim digests and statement
digests carrying their preconditions, `CclQP`, `SdQP`, its DA roots' loops `Loop100Q`), the honest
memory of the re-chosen tree reading its load equations and nothing else off frames
(`honest_of_mainCT'`). -/
theorem decode_stmts {S : BlakeSem} (hB : B2C.B2HypsB S) {Ha : List UInt8 → Option Digest}
    {Ht : List UInt8 → Digest} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode seed s w)
    (hlim : End.Limits s w) {κ : ℕ} {VsGood : B1.VerifySub.VsData → B1.VerifySub.VsRunC → Prop}
    (hW : B1.Main.MainWordsOkC S B2C.fs Ha κ VsGood 0 (B1.Main.honestWordsC Ht seed s w))
    {hdr : E × E} {rd0 : Reader} {T0 : Tree} {ν : ℕ → String → Val → V → E}
    {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop}
    {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC}
    (hv : T0.ValidB S coreProgram rd0 [] [])
    (hQ : B1.Main.MainQ VsQ vr (CclQP Ha) (SdQP Ha) B1.Main.Loop100Q
      (B1.Main.mainIQ B2C.fs 0 (B1.Main.honestWordsC Ht seed s w)) B2C.fs w.children.length 0
      (B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 (B1.Main.honestWordsC Ht seed s w))) rd0 T0)
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read [] [])
    (htot : T0.total B2C.fs < 2 ^ 32)
    (hmem : B1.Main.MemL rd0 (mainIn B2C.fs 0 (B1.Main.honestWordsC Ht seed s w)))
    (himg : ∀ (a : K) (x : E), (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)).read a = some x → x = 0 ∨ rd0 a = some x ∨
          ∃ I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T0, ∃ i, I.Frame B2C.fs i ∧ a = Parameters.gpow i) :
    ∀ c (hc : c < w.children.length),
      B1.Main.kidStmt (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read
        (B1.Main.frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
          (T0.retemp coreProgram B2C.fs ν 0))))
        (B1.Main.gLog (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
          (T0.retemp coreProgram B2C.fs ν 0)) (.n 58)))
        (B1.Main.countOf (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read
          (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)))) c =
        w.children[c].statement := by
  set W := B1.Main.honestWordsC Ht seed s w with hWdef
  obtain ⟨bufs, ks, hT0, hnc⟩ := hQ
  have hbufs : bufs = W.sizes := main_bufs_eq hW hT0 rfl hH.bufsOk
  subst hbufs
  obtain ⟨fLx, fLs, fMd, fdaC, fT, fcov, flxT, fspT, fdaR, fcar, fwr⟩ :=
    mainFrame_words hB hT0 hH hlim (Ht := Ht) (seed := seed) rfl
  have hboth : ∀ q ∈ T0.loadEqns coreProgram, (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read q.1 = some q.2 ∧ rd0 q.1 = some q.2 :=
    fun q hq => ⟨honest_read_loadEqns hH.toHonestB q hq, loadEqns_read_of_validB T0 hv q hq⟩
  have hdl : ∀ c' ∈ w.children, c'.statement.defer.cells.length = 53 := by
    intro c' hc'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have := (hW.children i hi).dlen
    have hr : W.child i = B1.Main.childWordsOfC Ht seed w.children[i] (B1.Main.hbase s w i) := by
      simp only [hWdef, B1.Main.honestWordsC, hi, ↓reduceDIte]
    rw [hr] at this
    exact this
  have hcw := fun c' (hc' : c' < w.children.length) =>
    child_words_of_mainQ (ν := ν) (hdr := hdr) hW hT0 hnc hboth hmem hdl hc'
  intro c hc
  have hwr : ∀ c' ≤ w.children.length,
      (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)).read ((B1.Main.frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)))).written.limb 0 * Parameters.gpow c') =
        some (gen ^ B1.Main.hbase s w c') := by
    intro c' hc'
    rw [fwr]
    rcases Nat.lt_or_ge c' w.children.length with h | h
    · exact (hcw c' h).2.2.2.2.1
    · have e : c' = (w.children.length - 1) + 1 := by omega
      rw [e]
      exact (hcw _ (by omega)).2.2.2.2.2
  have hcnt := countOf_honest hlim hwr
  obtain ⟨hX, hS, hD, hdef, -, -⟩ := hcw c hc
  have hcl : W.cov.length = W.total := B1.Main.honestWordsC_cov_length Ht seed
  have hcl' : W.cov.length = s.claims.xmss.length + (B1.Main.planX s w).2.length +
      (s.claims.sphincs.length + (B1.Main.planS s w).2.length) +
      (s.claims.da.length + (B1.Main.planD s w).2.length) := B1.Main.honestWordsC_cov_length Ht seed
  refine kidStmt_honest Ht seed hrel hlim hc fLx fLs fMd fT fdaC (hcnt c hc.le) (hcnt (c + 1) hc)
    ?_ ?_ ?_ ?_ ?_
  · rw [fcov, fT]
    intro s' hs'
    exact cover_image hT0 htot hmem himg hcl s' (by omega)
  · rw [fcov, flxT]; exact hX
  · rw [fcov, fspT]; exact hS
  · rw [fdaC, fcov, fdaR]; exact hD
  · rw [fcar]; exact hdef

end
end LeanVM.E2E.Complete
