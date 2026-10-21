/-
  LeanVM.Guest.B1.Comp.Whir.Cap

  The Merkle cap over a completeness model: `hash_cap_node` and `verify_merkle_cap` at its five
  depths, with its loops.
-/

module

public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.Whir.Cap

/-!
# The Merkle cap over a completeness model

The backward half of `verify_merkle_cap_iff` over a `CompModel`: a cap node is hashed when the
model answers its children's bytes (`CapHashedC CM`, the deployed `CapHashed` at
`CompModel.deployed`), its row the model's (`compress_of_hashPairC`, the dual of
`compress_of_hashPair`). The blocks hold under any semantics from their rows
(`hashCapNodeT_completeB`, `capSideT_completeB`, `capLoop_step_bwdB`, their honest outputs the
words loaded after the row, `hcnValsM`), and `verify_merkle_cap_comp` from
`MeaningVerifyMerkleCapComp CM D`, with the five specializations
`verify_merkle_cap_L{4..8}_comp`; at `CompModel.deployed` the deployed backward direction
(`verify_merkle_cap_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## A node's row -/

/-- **One cap node's row over a completeness model** (the dual of `compress_of_hashPair`): the
block of two digests checks from the IV to the model's answer for their bytes. -/
theorem compress_of_hashPairC (CM : CompModel) (l r : Digest) {d : Digest}
    (hd : CM.H (digestBytes l ++ digestBytes r) = some d) :
    CM.sem.check ![(digestScalars l).1, (digestScalars l).2, (digestScalars r).1,
      (digestScalars r).2] Value.ivCells.1 Value.ivCells.2 (digestScalars d).1 (digestScalars d).2
      (metadataCell 64 true) := by
  rw [← blockBytes_digests] at hd
  refine CM.check_one (fun i => ?_) hd
  fin_cases i
  exacts [(isCanonical128_digestScalars l).1, (isCanonical128_digestScalars l).2,
    (isCanonical128_digestScalars r).1, (isCanonical128_digestScalars r).2]

/-- Cap node `i` is the model's answer for its children's digests (`CapHashed`). -/
def CapHashedC (CM : CompModel) (rd : Reader) (cap : E) (i : ℕ) : Prop :=
  ∃ l r d : Digest, CapCell rd cap (2 * i) l ∧ CapCell rd cap (2 * i + 1) r ∧
    CM.H (digestBytes l ++ digestBytes r) = some d ∧ CapCell rd cap i d

theorem capHashedC_deployed {cap : E} {i : ℕ} :
    CapHashedC CompModel.deployed rd cap i ↔ CapHashed rd cap i := by
  simp only [CapHashedC, CapHashed, CompModel.deployed, Option.some.injEq, hashPair]
  exact ⟨fun ⟨l, r, d, hl, hr, hd, hc⟩ => ⟨l, r, hl, hr, hd ▸ hc⟩,
    fun ⟨l, r, hl, hr, hc⟩ => ⟨l, r, _, hl, hr, rfl, hc⟩⟩

/-! ## `hash_cap_node`, under any semantics -/

/-- What `hash_cap_node(cap, c)` asks under `S` (`HashCapSem`). -/
def HashCapSemB (S : BlakeSem) (rd : Reader) (cap c : E) : Prop :=
  ∃ m0 m1 m2 m3 o0 o1 : E, LoadHolds rd (cap * (c * c * (c * c))) 0 m0 ∧
    LoadHolds rd (cap * (c * c * (c * c))) 1 m1 ∧ LoadHolds rd (cap * (c * c * (c * c))) 2 m2 ∧
    LoadHolds rd (cap * (c * c * (c * c))) 3 m3 ∧
    S.check ![m0, m1, m2, m3] Value.ivCells.1 Value.ivCells.2 o0 o1 (metadataCell 64 true) ∧
    LoadHolds rd (cap * (c * c)) 0 o0 ∧ LoadHolds rd (cap * (gen * c * c)) 0 o1

/-- The honest values of `hashCapNodeT`, the output the words stored after the row (`hcnVals`). -/
def hcnValsM (rd : Reader) (cap c : E) : List E :=
  [c * c, c * c * (c * c), cap * (c * c * (c * c)), memAt rd (cap * (c * c * (c * c))) 0,
    memAt rd (cap * (c * c * (c * c))) 1, memAt rd (cap * (c * c * (c * c))) 2,
    memAt rd (cap * (c * c * (c * c))) 3, Value.ivCells.1, Value.ivCells.2, metadataCell 64 true,
    memAt rd (cap * (c * c)) 0, memAt rd (cap * (gen * c * c)) 0,
    c * c, cap * (c * c), gen, gen * c, gen * c * c, cap * (gen * c * c)]

theorem hashCapNodeT_completeB {S : BlakeSem} {cap c : V} {b : ℕ} {next : Prop}
    {kret : List E → Prop}
    (hv : ∀ k < 18, σ (.n (b + k)) = (hcnValsM rd (σ cap) (σ c)).getD k 0)
    (hs : HashCapSemB S rd (σ cap) (σ c)) (hn : next) :
    Stmt.HoldsListB S C rd σ (hashCapNodeT cap c b) next kret := by
  obtain ⟨m0, m1, m2, m3, o0, o1, a0, a1, a2, a3, hc, l0, l1⟩ := hs
  have v : ∀ k (hk : k < 18), σ (.n (b + k)) = (hcnValsM rd (σ cap) (σ c)).getD k 0 := hv
  have v0 := v 0 (by omega)
  have v1 := v 1 (by omega)
  have v2 := v 2 (by omega)
  have v3 := v 3 (by omega)
  have v4 := v 4 (by omega)
  have v5 := v 5 (by omega)
  have v6 := v 6 (by omega)
  have v7 := v 7 (by omega)
  have v8 := v 8 (by omega)
  have v9 := v 9 (by omega)
  have v10 := v 10 (by omega)
  have v11 := v 11 (by omega)
  have v12 := v 12 (by omega)
  have v13 := v 13 (by omega)
  have v14 := v 14 (by omega)
  have v15 := v 15 (by omega)
  have v16 := v 16 (by omega)
  have v17 := v 17 (by omega)
  simp only [hcnValsM, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero,
    memAt_of_load a0, memAt_of_load a1, memAt_of_load a2, memAt_of_load a3, memAt_of_load l0,
    memAt_of_load l1] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
  simp only [hashCapNodeT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_iv0, word_iv1,
    word_md64, word_gen]
  rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]
  exact ⟨rfl, rfl, rfl, a0, a1, a2, a3, rfl, rfl, rfl, hc, rfl, rfl, l0, rfl, rfl, rfl, rfl, l1, hn⟩

/-- **`hash_cap_node` at `g^i` over a completeness model** (`hashCapSem_gen_pow`'s backward
half). -/
theorem hashCapSemB_of_capHashedC {CM : CompModel} (rd : Reader) (cap : E) (i : ℕ)
    (h : CapHashedC CM rd cap i) : HashCapSemB CM.sem rd cap (gen ^ i) := by
  have e4 : gen ^ i * gen ^ i * (gen ^ i * gen ^ i) = gen ^ (4 * i) := by
    simp only [gen_pow_mul_gen_pow]; congr 1; ring
  have e2 : gen ^ i * gen ^ i = gen ^ (2 * i) := by rw [gen_pow_mul_gen_pow]; congr 1; ring
  have e2' : gen * gen ^ i * gen ^ i = gen ^ (2 * i + 1) := by
    rw [← pow_succ', gen_pow_mul_gen_pow]; congr 1; ring
  simp only [HashCapSemB]
  rw [e4, e2', e2]
  simp only [loadHolds_mul_gen_pow, Nat.add_zero, show 4 * i = 2 * (2 * i) by ring,
    show 2 * (2 * i) + 2 = 2 * (2 * i + 1) by ring,
    show 2 * (2 * i) + 3 = 2 * (2 * i + 1) + 1 by ring]
  obtain ⟨l, r, d, ⟨l0, l1⟩, ⟨r0, r1⟩, hd, h0, h1⟩ := h
  exact ⟨_, _, _, _, _, _, l0, l1, r0, r1, compress_of_hashPairC CM l r hd, h0, h1⟩

/-! ## The loop of `verify_merkle_cap`, under any semantics -/

/-- What one side asks under `S` (`CapSideSem`). -/
def CapSideSemB (S : BlakeSem) (rd : Reader) (flags cap x c : E) : Prop :=
  ∃ f, LoadHolds rd (flags * c) 0 f ∧ IsInK f ∧
    (f ≠ 0 → LoadHolds rd (flags * x) 0 1 ∧ HashCapSemB S rd cap c)

/-- The honest values of `capSideT` (`capSideVals`, the outputs the stored words). -/
def capSideValsM (rd : Reader) (flags cap x c : E) : List E :=
  [flags * c, memAt rd (flags * c) 0, 1, flags * x] ++ hcnValsM rd cap c

theorem length_capSideValsM (rd : Reader) (flags cap x c : E) :
    (capSideValsM rd flags cap x c).length = 22 := rfl

theorem holdsB_capSideT {S : BlakeSem} (flags cap x c : V) (b : ℕ) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ (capSideT flags cap x c b) next kret ↔
      Stmt.HoldsListB S C rd σ (capSideT flags cap x c b) True kret ∧ next :=
  holdsListB_noRet _ rfl next kret

theorem capSideT_completeB {S : BlakeSem} {flags cap x c : V} {b : ℕ} {kret : List E → Prop}
    (hv : ∀ k < 22, σ (.n (b + k)) = (capSideValsM rd (σ flags) (σ cap) (σ x) (σ c)).getD k 0)
    (hs : CapSideSemB S rd (σ flags) (σ cap) (σ x) (σ c)) :
    Stmt.HoldsListB S C rd σ (capSideT flags cap x c b) True kret := by
  obtain ⟨f, lf, hK, hnz⟩ := hs
  have v0 : σ (.n b) = σ flags * σ c := hv 0 (by omega)
  have v1 : σ (.n (b + 1)) = f := by rw [hv 1 (by omega)]; exact memAt_of_load lf
  have v2 : σ (.n (b + 2)) = 1 := hv 2 (by omega)
  have v3 : σ (.n (b + 3)) = σ flags * σ x := hv 3 (by omega)
  simp only [capSideT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, holdsListB_append, word_one]
  refine ⟨v0, by rw [v0, v1]; exact lf, by rw [v1]; exact hK, fun _ => trivial, fun hf => ?_⟩
  rw [v1] at hf
  obtain ⟨l1, hh⟩ := hnz hf
  refine ⟨v2, v3, by rw [v3, v2]; exact l1, hashCapNodeT_completeB (fun k hk => ?_) hh trivial⟩
  rw [show b + 4 + k = b + (k + 4) by ring, hv (k + 4) (by omega), capSideValsM,
    List.getD_append_right _ _ _ _ (by simp)]
  rfl

/-- The loop's body at the parent `x` under `S` (`CapLoopBody`). -/
def CapLoopBodyB (S : BlakeSem) (rd : Reader) (flags cap x : E) : Prop :=
  CapSideSemB S rd flags cap x (x * x) ∧ CapSideSemB S rd flags cap x (x * x * gen)

/-- The honest valuation of one iteration (`capLoopSig`). -/
def capLoopSigM (rd : Reader) (x N flags cap : E) : Val :=
  setl (setl (setl (setl (setl (Val.ofArgs [x, N, flags, cap]) 4 [x * x]) 5
    (capSideValsM rd flags cap x (x * x))) 27 [x * x, gen, x * x * gen]) 30
    (capSideValsM rd flags cap x (x * x * gen))) 52 [gen, x * gen, x * gen + N, gen, x * gen]

/-- One iteration of the cap's loop under any semantics, backward (`capLoop_step`'s backward
half). -/
theorem capLoop_step_bwdB {S : BlakeSem} {loop : String} {fn : Fn}
    (hfind : coreProgram.find? loop = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hb : fn.body = capLoopBody loop) (rd : Reader) (N flags cap x : E)
    (hB : CapLoopBodyB S rd flags cap x) (hK : IsInK (x * gen + N))
    (hcall : x * gen + N ≠ 0 → coreProgram.RelB S rd loop (x * gen :: [N, flags, cap]) []) :
    ∃ fn, coreProgram.find? loop = some fn ∧
      fn.SemB S (coreProgram.RelB S rd) rd (x :: [N, flags, cap]) [] := by
  refine ⟨fn, hfind, ?_⟩
  obtain ⟨s0, s1⟩ := hB
  simp only [Fn.SemB]
  rw [hp, hb, capLoopBody]
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil, and_true, word_gen]
  set τ := capLoopSigM rd x N flags cap
  have hv0 : ∀ k < 22, τ (.n (5 + k)) = (capSideValsM rd flags cap x (x * x)).getD k 0 :=
    fun k hk => by
      simp only [τ, capLoopSigM, setl, length_capSideValsM]
      rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega),
        set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hv1 : ∀ k < 22, τ (.n (30 + k)) = (capSideValsM rd flags cap x (x * x * gen)).getD k 0 :=
    fun k hk => by
      simp only [τ, capLoopSigM, setl, length_capSideValsM]
      rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have a0 : τ (.n 0) = x := by simp only [τ, capLoopSigM]; b1_look
  have a1 : τ (.n 1) = N := by simp only [τ, capLoopSigM]; b1_look
  have a2 : τ (.n 2) = flags := by simp only [τ, capLoopSigM]; b1_look
  have a3 : τ (.n 3) = cap := by simp only [τ, capLoopSigM]; b1_look
  have a4 : τ (.n 4) = x * x := by simp only [τ, capLoopSigM]; b1_look
  have a27 : τ (.n 27) = x * x := by simp only [τ, capLoopSigM]; b1_look
  have a28 : τ (.n 28) = gen := by simp only [τ, capLoopSigM]; b1_look
  have a29 : τ (.n 29) = x * x * gen := by simp only [τ, capLoopSigM]; b1_look
  have a52 : τ (.n 52) = gen := by simp only [τ, capLoopSigM]; b1_look
  have a53 : τ (.n 53) = x * gen := by simp only [τ, capLoopSigM]; b1_look
  have a54 : τ (.n 54) = x * gen + N := by simp only [τ, capLoopSigM]; b1_look
  have a55 : τ (.n 55) = gen := by simp only [τ, capLoopSigM]; b1_look
  have a56 : τ (.n 56) = x * gen := by simp only [τ, capLoopSigM]; b1_look
  refine ⟨τ, by rw [a0, a1, a2, a3], by rw [a4, a0], (holdsB_capSideT _ _ _ _ _ _ _).mpr
    ⟨capSideT_completeB ?_ ?_, by rw [a27, a0], by rw [a28], by rw [a29, a27, a28],
      (holdsB_capSideT _ _ _ _ _ _ _).mpr ⟨capSideT_completeB ?_ ?_, by rw [a52],
        by rw [a53, a0, a52], by rw [a54, a53, a1], by rw [a55], by rw [a56, a0, a55],
        by rw [a54]; exact hK, by rw [a54, a56, a1, a2, a3]; exact hcall⟩⟩⟩
  · intro k hk; rw [hv0 k hk, a2, a3, a0, a4]
  · rw [a2, a3, a0, a4]; exact s0
  · intro k hk; rw [hv1 k hk, a2, a3, a0, a29]
  · rw [a2, a3, a0, a29]; exact s1

/-! ## `verify_merkle_cap` over a completeness model -/

/-- Node `c` of the cap's interior over a model: its flag in `K`, and if nonzero its parent's flag
`1` and it the model's hash of its children (`CapFlagged`). -/
def CapFlaggedC (CM : CompModel) (rd : Reader) (flags cap : E) (c : ℕ) : Prop :=
  ∃ f, LoadHolds rd flags c f ∧ IsInK f ∧
    (f ≠ 0 → LoadHolds rd flags (c / 2) 1 ∧ CapHashedC CM rd cap c)

theorem capFlaggedC_deployed {flags cap : E} {c : ℕ} :
    CapFlaggedC CompModel.deployed rd flags cap c ↔ CapFlagged rd flags cap c := by
  simp only [CapFlaggedC, CapFlagged, capHashedC_deployed]

/-- **`verify_merkle_cap(cap, flags, D)` over a completeness model** (`MeaningVerifyMerkleCap`,
every hashed node the model's answer). -/
def MeaningVerifyMerkleCapComp (CM : CompModel) (D : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags], rets =>
      LoadHolds rd flags 1 1 ∧ CapHashedC CM rd cap 1 ∧
        (∀ c, 2 ≤ c → c < 2 ^ D → CapFlaggedC CM rd flags cap c) ∧
        ∃ r, CapCell rd cap 1 r ∧ rets = [(digestScalars r).1, (digestScalars r).2]
  | _, _ => False

theorem meaningVerifyMerkleCapComp_deployed (D : ℕ) (rd : Reader) (args rets : List E) :
    MeaningVerifyMerkleCapComp CompModel.deployed D rd args rets ↔
      MeaningVerifyMerkleCap D rd args rets := by
  match args with
  | [cap, flags] =>
    simp only [MeaningVerifyMerkleCapComp, MeaningVerifyMerkleCap, capHashedC_deployed,
      capFlaggedC_deployed]
  | [] | [_] | _ :: _ :: _ :: _ => exact Iff.rfl

/-- One side at the parent `g^p` over a model: the child `2p + s` (`capSideSem_gen_pow`'s
backward half). -/
theorem capSideSemB_gen_pow {CM : CompModel} (rd : Reader) (flags cap : E) (p s : ℕ) (hs : s < 2)
    (h : CapFlaggedC CM rd flags cap (2 * p + s)) :
    CapSideSemB CM.sem rd flags cap (gen ^ p) (gen ^ (2 * p + s)) := by
  have hdiv : (2 * p + s) / 2 = p := by omega
  obtain ⟨f, lf, hK, hnz⟩ := h
  refine ⟨f, (loadHolds_gen_pow _ _ _ _).mpr lf, hK, fun hf => ?_⟩
  obtain ⟨l1, hh⟩ := hnz hf
  rw [hdiv] at l1
  exact ⟨(loadHolds_gen_pow _ _ _ _).mpr l1, hashCapSemB_of_capHashedC rd cap _ hh⟩

theorem capLoopBodyB_gen_pow {CM : CompModel} (rd : Reader) (flags cap : E) (p : ℕ)
    (h0 : CapFlaggedC CM rd flags cap (2 * p)) (h1 : CapFlaggedC CM rd flags cap (2 * p + 1)) :
    CapLoopBodyB CM.sem rd flags cap (gen ^ p) := by
  have e0 : gen ^ p * gen ^ p = gen ^ (2 * p + 0) := by rw [gen_pow_mul_gen_pow]; congr 1; ring
  have e1 : gen ^ p * gen ^ p * gen = gen ^ (2 * p + 1) := by
    rw [gen_pow_mul_gen_pow, ← pow_succ]; congr 1; ring
  rw [CapLoopBodyB, e1, e0]
  exact ⟨capSideSemB_gen_pow rd flags cap p 0 (by omega) h0,
    capSideSemB_gen_pow rd flags cap p 1 (by omega) h1⟩

/-- **`verify_merkle_cap` at a depth `2 ≤ D ≤ 8` is complete over a completeness model**, for a
compiled function whose body is `vmcBody` with its loop helper's body `capLoopBody`. -/
theorem verify_merkle_cap_comp {CM : CompModel} {name loop : String} {f lf : Fn} (D : ℕ)
    (hD : 2 ≤ D) (hD8 : D ≤ 8) (hfind : coreProgram.find? name = some f)
    (hp : f.params = [.n 0, .n 1])
    (hb : f.body = vmcBody (word (gSquaresBits.getD (D - 1) 0) 0 0) loop)
    (hlf : coreProgram.find? loop = some lf) (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3])
    (hlb : lf.body = capLoopBody loop) (rd : Reader) (args rets : List E)
    (hm : MeaningVerifyMerkleCapComp CM D rd args rets) :
    coreProgram.RelB CM.sem rd name args rets := by
  have hW : word (gSquaresBits.getD (D - 1) 0) 0 0 = gen ^ 2 ^ (D - 1) :=
    word_gSquares (by simp only [sizeBits]; omega)
  have hm1 : 1 < 2 ^ (D - 1) := Nat.one_lt_two_pow (by omega)
  obtain ⟨cap, flags, rfl⟩ : ∃ cap flags, args = [cap, flags] := by
    match args, hm with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨l13, hroot, hint, rt, hrt, hret⟩ := hm
  obtain ⟨l, r, d, ⟨a0, a1⟩, ⟨b0, b1⟩, hd, ⟨o0, o1⟩⟩ := hroot
  have hrt' := hrt.unique ⟨o0, o1⟩
  subst hrt' hret
  have hloop : coreProgram.RelB CM.sem rd loop [gen, gen ^ 2 ^ (D - 1), flags, cap] [] := by
    have := Digest.loopB_bwd (k := 1) (m := 2 ^ (D - 1)) (S := CM.sem) (rd := rd) (f := loop)
      (ps := [gen ^ 2 ^ (D - 1), flags, cap]) (N := gen ^ 2 ^ (D - 1))
      (B := fun x => CapLoopBodyB CM.sem rd flags cap x)
      (fun x hB hK hc => capLoop_step_bwdB hlf hlp hlb rd _ flags cap x hB hK hc) hm1 rfl
      (fun j h1 h2 => capLoopBodyB_gen_pow rd flags cap j
        (hint _ (by omega) (by rw [show 2 ^ D = 2 * 2 ^ (D - 1) by rw [← pow_succ']; congr 1; omega]; omega))
        (hint _ (by omega) (by rw [show 2 ^ D = 2 * 2 ^ (D - 1) by rw [← pow_succ']; congr 1; omega]; omega)))
    rwa [pow_one] at this
  rw [relB_iff_sem hfind, hb, hp, vmcBody]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_iv0,
    word_iv1, word_md64, word_one, word_gen, word_sixteen, hW]
  refine ⟨setl (Val.ofArgs [cap, flags]) 2 [gen ^ 4, cap * gen ^ 4, (digestScalars l).1,
    (digestScalars l).2, (digestScalars r).1, (digestScalars r).2, Value.ivCells.1,
    Value.ivCells.2, metadataCell 64 true, (digestScalars rt).1,
    (digestScalars rt).2, 1, gen, gen ^ 2 ^ (D - 1), gen + gen ^ 2 ^ (D - 1), gen,
    gen ^ 2 ^ (D - 1), (digestScalars rt).1, (digestScalars rt).2],
    by b1_look, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  all_goals b1_look
  · simpa [loadHolds_mul_gen_pow] using a0
  · simpa [loadHolds_mul_gen_pow] using a1
  · simpa [loadHolds_mul_gen_pow] using b0
  · simpa [loadHolds_mul_gen_pow] using b1
  · exact compress_of_hashPairC CM l r hd
  · simpa using o0
  · simpa using o1
  · exact l13
  · have h1 := isInK_add (gen_pow_isInK 1) (gen_pow_isInK (2 ^ (D - 1)))
    rwa [pow_one] at h1
  · intro _; exact hloop
  · simpa using o0
  · simpa using o1

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L4_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningVerifyMerkleCapComp CM 4 rd args rets) :
    coreProgram.RelB CM.sem rd "verify_merkle_cap__L4" args rets :=
  verify_merkle_cap_comp (loop := "__loop454") 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1006) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets hm

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L5_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningVerifyMerkleCapComp CM 5 rd args rets) :
    coreProgram.RelB CM.sem rd "verify_merkle_cap__L5" args rets :=
  verify_merkle_cap_comp (loop := "__loop433") 5 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 978) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets hm

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L6_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningVerifyMerkleCapComp CM 6 rd args rets) :
    coreProgram.RelB CM.sem rd "verify_merkle_cap__L6" args rets :=
  verify_merkle_cap_comp (loop := "__loop431") 6 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 975) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets hm

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L7_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningVerifyMerkleCapComp CM 7 rd args rets) :
    coreProgram.RelB CM.sem rd "verify_merkle_cap__L7" args rets :=
  verify_merkle_cap_comp (loop := "__loop456") 7 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 683) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1008) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets hm

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L8_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningVerifyMerkleCapComp CM 8 rd args rets) :
    coreProgram.RelB CM.sem rd "verify_merkle_cap__L8" args rets :=
  verify_merkle_cap_comp (loop := "__loop429") 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 579) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 972) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets hm

/-! ## At the deployed model -/

theorem verify_merkle_cap_of_comp {name loop : String} {f lf : Fn} (D : ℕ) (hD : 2 ≤ D)
    (hD8 : D ≤ 8) (hfind : coreProgram.find? name = some f) (hp : f.params = [.n 0, .n 1])
    (hb : f.body = vmcBody (word (gSquaresBits.getD (D - 1) 0) 0 0) loop)
    (hlf : coreProgram.find? loop = some lf) (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3])
    (hlb : lf.body = capLoopBody loop) (rd : Reader) (args rets : List E)
    (h : MeaningVerifyMerkleCap D rd args rets) : coreProgram.Rel rd name args rets := by
  rw [← relB_deployed]
  exact verify_merkle_cap_comp (CM := CompModel.deployed) D hD hD8 hfind hp hb hlf hlp hlb rd
    args rets ((meaningVerifyMerkleCapComp_deployed D rd args rets).mpr h)

end
end LeanVM.Guest.B1
