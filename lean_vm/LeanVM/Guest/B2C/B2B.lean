/-
  LeanVM.Guest.B2C.B2B

  B2's completeness (`B2.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.B2
public import LeanVM.Guest.B2C.CplAllB
public import LeanVM.Guest.B2C.TableB
public import LeanVM.Guest.MemoryB
public import LeanVM.Guest.SoundB

/-!
# B2's completeness under any `BLAKE2S` semantics

`B2.lean`'s `B2Hyps` and `InstRuns` with `S : BlakeSem` a parameter (`B2HypsB`: every function
runs under `S`, `CplRunB S`, and the frames of the honest memory under `S` hold; `InstRunsB`), and
B2 itself: every running instance runs (`instB_runs`), `main` from its entry to the end within
the counts (`mainB_runC`, `b2B_complete`, `b2B_count`: a halting run under `S` counts, by
`runCountB S`, at most `cnt T op` of each opcode).

* `b2HypsB_deployed`, `instRunsB_deployed`: at `blakeDeployed`, they are `B2.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.End (mainEntry JumpTables)

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **What B2's completeness rests on**: each function's completeness check (`cplRunB_of_ok`) and
the frames of the honest memory. -/
structure B2HypsB : Prop where
  run : ∀ j, 1 ≤ j → j < nFns → CplRunB S j
  frame : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    HonestAtB S coreProgram fs H C hdr T cert rd [] [] → ∀ I ∈ honestInsts coreProgram fs H hdr T,
      ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ j, idxOf f = some j → ∀ es vs,
        walk σ (coreOf j).body = .ret es vs →
          FrameHolds (honest coreProgram fs H C hdr T) j I.fp σ es vs I.kidFps I.hdr

/-- Each function's completeness check gives its run (`cplRunB_of`). -/
theorem cplRunB_of_ok (hok : ∀ j, 1 ≤ j → j < nFns → CplOk j) : ∀ j, 1 ≤ j → j < nFns → CplRunB S j :=
  fun j h1 h2 => cplRunB_of h1 h2 (hok j h1 h2)

/-! ## Functions and their callees -/

private theorem idxOf_of_find {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) :
    ∃ j, idxOf f = some j := by
  cases hj : idxOf f with
  | none =>
    unfold idxOf at hj
    rw [Option.map_eq_none_iff] at hj
    rw [find?_none hj] at hf
    cases hf
  | some j => exact ⟨j, rfl⟩

/-- The callees of the frames set up: one per call, of its function, valid when entered. -/
theorem kidsValidB_get {P : Core.Program} {rd : Reader} {σ : Val} : ∀ {cs : List Memory.Call} {ks : List Memory.Tree},
    Tree.KidsValidB S P rd σ cs ks → ks.length = cs.length ∧ ∀ (i : ℕ) (c : Memory.Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧ (c.taken = true → k.ValidB S P rd (c.args.map σ) (c.rets.map σ))
  | [], [], _ => ⟨rfl, fun i c h => by simp at h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩ => by
    obtain ⟨hl, ih⟩ := kidsValidB_get h
    refine ⟨by simp [hl], fun i c' hc => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨k, rfl, hn, fun ht => ?_⟩
      simp only [ht, ↓reduceIte] at hk
      exact hk
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact ih i c' hc

private theorem ite_intro_pos {p : Prop} [Decidable p] {a b : Prop} (hp : p) (ha : a) :
    if p then a else b := by
  split
  · exact ha
  · contradiction

private theorem ite_intro_neg {p : Prop} [Decidable p] {a b : Prop} (hp : ¬p) (hb : b) :
    if p then a else b := by
  split
  · contradiction
  · exact hb

private theorem ite_elim_pos {p : Prop} [Decidable p] {a b : Prop} (hp : p) (h : if p then a else b) : a := by
  split at h
  · exact h
  · contradiction

private theorem ite_elim_neg {p : Prop} [Decidable p] {a b : Prop} (hp : ¬p) (h : if p then a else b) : b := by
  split at h
  · contradiction
  · exact h

/-! ## The prologue -/

/-- **The jump table's prologue, counted**: `__jump_tables`' `SET`s from `(g^0, 1)` to `main`'s
entry. -/
theorem runCB_jumpTables {κ : ℕ} {L : MemImage κ} (h : JumpTables L) :
    RunCB S guest L ⟨gpow 0, 1⟩ ⟨gpow mainEntry, 1⟩ jtSets := by
  have hwalk : ∀ i ≤ Data.f0.len, RunCB S guest L ⟨gpow 0, 1⟩ ⟨gpow i, 1⟩
      (fun op => if op = .setConstant then i else 0) := by
    intro i
    induction i with
    | zero =>
      intro _
      have e : (fun op : Opcode => if op = .setConstant then 0 else 0) = 0 := by
        funext op; split <;> rfl
      rw [e]
      exact RunCB.refl _
    | succ i ih =>
      intro hi
      obtain ⟨o, k0, k1, k2, hins, hq⟩ := End.f0_instr (show i < Data.f0.len by omega)
      have hf := End.f0_fetch (show i < Data.f0.len by omega)
      rw [hins] at hf
      have hH : HoldsB S L i 1 (.set o k0 k1 k2) := by
        show L.read (1 * gpow o) = some (OInstr.imm k0 k1 k2)
        rw [End.gpow_mul_one]
        exact h _ hq
      have := (ih (by omega)).trans (runCB_fallThrough hf (End.f0_pc_lt (by omega)) rfl hH)
      have e : (fun op : Opcode => if op = .setConstant then i + 1 else 0) =
          (fun op : Opcode => if op = .setConstant then i else 0) +
            (fun op ↦ if op = (OInstr.set o k0 k1 k2).toInstr.opcode then 1 else 0) := by
        funext op
        by_cases hop : op = .setConstant <;> simp [hop, OInstr.toInstr, Instr.opcode]
      rw [e]
      exact this
  have := hwalk _ le_rfl
  have e : (fun op : Opcode => if op = .setConstant then Data.f0.len else 0) = jtSets := by
    funext op
    unfold jtSets
    rfl
  rw [e] at this
  exact this

/-! ## The instances -/

variable (S) in
/-- What an instance's run gives: its return registers (`main`: the final ones), a counted run
there from its entry at its frame within its subtree's weight, and its returns after its
arguments. -/
def InstRunsB {κ : ℕ} (L : MemImage κ) (I : Inst) (args rets : List E) : Prop :=
  ∃ (r : Regs K) (c : Opcode → ℕ),
    (if I.t.name = "main" then r = Regs.final guest else retRegs L (gpow I.fp) = some r) ∧
    RunCB S guest L ⟨gpow (entryOf I.t.name), gpow I.fp⟩ r c ∧ (∀ op, c op ≤ weightV (fun f σ ↦ pathCountN f σ op) I.t) ∧
    ∀ k (hk : k < rets.length), L.read (gpow (I.fp + (2 + args.length + k))) = some rets[k]

section Insts

variable (h : B2HypsB S) {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram fs H C hdr T cert rd [] [])
include h hname hH

/-- **Every instance that runs runs**, by induction on the words its subtree allocates. -/
theorem instB_runs : ∀ n, ∀ I ∈ honestInsts coreProgram fs H hdr T, I.t.total fs < n →
    (I.t.name = "main" → I.fp = 0) → ∀ args rets,
      I.t.ValidB S coreProgram (honest coreProgram fs H C hdr T).read args rets →
        InstRunsB S (honest coreProgram fs H C hdr T) I args rets
  | 0, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, I, hI, hn, hm, args, rets, hv => by
    set L := honest coreProgram fs H C hdr T with hL
    rcases hti : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hti] at hv
      obtain ⟨fn, hf, hpar, es, vs, hw, hrets, hev, hk⟩ := hv
      obtain ⟨j, hj⟩ := idxOf_of_find hf
      obtain ⟨i, rfl, hi, hn', hfind, hcore, -, -, h1, hlt⟩ := fn_of_idx hj
      obtain rfl : fn = coreProgram[i] := Option.some.inj (hf.symm.trans hfind)
      have hw' : walk σ (coreOf (i + 1)).body = .ret es vs := by rw [hcore]; exact hw
      have hF := h.frame hdr rd T hname hH I hI f σ bufs kids hti (i + 1) hj es vs hw'
      have hkv := kidsValidB_get hk
      have hkids : I.t.kids = kids := by rw [hti]; rfl
      have hex : ∀ i' : ℕ, ∃ ci : Opcode → ℕ, (∀ (c : Memory.Call) (kfp : ℕ), (calls es)[i']? = some c →
          I.kidFps[i']? = some kfp → c.taken = true → (∃ r, retRegs L (gpow kfp) = some r ∧
            RunCB S guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r ci) ∧
            ∀ k (hk : k < c.rets.length),
              L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])) ∧
          ∀ op, ci op ≤ ((kids[i']?).map (weightV (fun f σ ↦ pathCountN f σ op))).getD 0 := by
        intro i'
        cases hc : (calls es)[i']? with
        | none => exact ⟨0, fun c _ h' => absurd h' (by simp), fun _ => Nat.zero_le _⟩
        | some c =>
          obtain ⟨k, hk', hkn, hkval⟩ := hkv.2 i' c hc
          by_cases htk : c.taken = true
          · obtain ⟨J, hJ, hJt, hJfp, -⟩ := honest_kid hI (k := k) (by rw [hkids]; exact hk')
            have hlt' : J.t.total fs < n := by
              have := total_lt_of_kid (f := f) (σ := σ) (bufs := bufs) hk'
              rw [hti] at hn
              rw [hJt]
              omega
            have hne : c.f ≠ "main" := calls_ne_main hfind hw (List.mem_of_getElem? hc)
            have hJn : J.t.name = c.f := by rw [hJt, hkn]
            obtain ⟨r, ci, hr, hrun, hle, hrets'⟩ := instB_runs n J hJ hlt'
              (fun hm' => absurd (hJn ▸ hm') hne) _ _ (hJt ▸ hkval htk)
            refine ⟨ci, fun c' kfp hc' hkfp _ => ?_, fun op => ?_⟩
            · obtain rfl : c' = c := (Option.some.inj hc').symm
              obtain rfl : kfp = J.fp := Option.some.inj (hkfp.symm.trans hJfp)
              rw [hJn] at hr hrun
              simp only [hne, ↓reduceIte] at hr
              refine ⟨⟨r, hr, hrun⟩, fun k' hk'' => ?_⟩
              have := hrets' k' (by simpa using hk'')
              simpa using this
            · rw [hk']
              simpa [hJt] using hle op
          · refine ⟨0, fun c' kfp hc' _ ht' => ?_, fun _ => Nat.zero_le _⟩
            obtain rfl : c' = c := (Option.some.inj hc').symm
            exact absurd ht' htk
      choose cf hcf using hex
      set ck := (List.range (calls es).length).map cf with hck
      have hK : KidsRunB S L σ es I.kidFps ck := by
        refine ⟨by simp [hck], fun i' c kfp hc hkfp ht => ?_⟩
        have hi' : i' < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
        have hget : ck.getD i' 0 = cf i' := by simp [hck, hi']
        rw [hget]
        exact (hcf i').1 c kfp hc hkfp ht
      have hjt : JumpTables L := jumpTablesB_honestC hH.toHonestB hname
      have hκ : logMem (T.total fs) ≤ 32 := hH.toHonestB.logMem_le
      have hmain : i + 1 = 1 → I.fp = 0 := fun h1' =>
        hm (by rw [hti]; exact (idx_one_iff hj).mp h1')
      obtain ⟨r, c, hr, hrun, hle, hrets'⟩ := h.run (i + 1) (by omega) hlt L hκ (End.jtHolds_of hjt) hjt
        I.fp hmain σ es vs hw' hev I.kidFps I.hdr hF ck hK
      have hname' : (coreOf (i + 1)).name = f := by rw [hcore]; exact hn'
      refine ⟨r, c, ?_, ?_, fun op => ?_, fun k hk' => ?_⟩
      · have key := idx_one_iff hj
        rw [hti]
        simp only [Tree.name]
        by_cases hfm : f = "main"
        · exact ite_intro_pos hfm (ite_elim_pos (key.mpr hfm) hr)
        · exact ite_intro_neg hfm (ite_elim_neg (fun h1' => hfm (key.mp h1')) hr)
      · rw [hti]
        simp only [Tree.name]
        rw [entryOf_of hj]
        exact hrun
      · rw [hti, weightV, weightVKids_eq_sumB, ← sum_range_getD _ kids, hkv.1]
        have hs : (ck.map (· op)).sum ≤
            ((List.range (calls es).length).map fun i' =>
              ((kids[i']?).map (weightV (fun f σ ↦ pathCountN f σ op))).getD 0).sum := by
          rw [hck, List.map_map]
          exact List.sum_le_sum fun i' _ => (hcf i').2 op
        have := hle op
        have hpc : pathCountN f σ op = pathCount (i + 1) σ op := by unfold pathCountN; rw [hj]
        rw [hpc]
        omega
      · subst hrets hpar
        have hk'' : k < vs.length := by simpa using hk'
        have := hrets' k hk''
        rw [hcore] at this
        simpa using this
    · rw [hti] at hv
      exact hv.elim

end Insts

/-! ## B2 -/

/-- `main` runs from its entry at frame `1` to the final registers, within the tree's weight. -/
theorem mainB_runC (h : B2HypsB S) {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
    (hH : HonestAtB S coreProgram fs H C hdr T cert rd [] []) :
    ∃ c : Opcode → ℕ, RunCB S guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest) c ∧
      ∀ op, c op ≤ weightV (fun f σ ↦ pathCountN f σ op) T := by
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hv : I.t.ValidB S coreProgram (honest coreProgram fs H C hdr T).read [] [] := by
    rw [hIt]; exact hH.toHonestB.valid_image
  obtain ⟨r, c, hr, hrun, hle, -⟩ := instB_runs h hname hH _ I hI (Nat.lt_succ_self _) (fun _ => hfp) [] [] hv
  rw [hIt] at hr hrun hle
  rw [hname] at hr hrun
  simp only [↓reduceIte] at hr
  subst hr
  rw [entryOf_main, hfp, show (gpow 0 : K) = 1 by rw [gpow, pow_zero]] at hrun
  exact ⟨c, hrun, hle⟩

/-- **B2**: on the honest memory, `main` runs from its entry to the final registers (`End`'s
`b2`). -/
theorem b2B_complete (h : B2HypsB S) : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    HonestAtB S coreProgram fs H C hdr T cert rd [] [] →
      ReachB S guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest) := by
  intro hdr rd T hname hH
  obtain ⟨c, hc, -⟩ := mainB_runC h hname hH
  exact hc.reach

/-- **B2, counted**: a halting run on the honest memory executes at most `cnt T op` instructions
of each opcode (`End`'s `count`). -/
theorem b2B_count (h : B2HypsB S) : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    HonestAtB S coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      runB S guest (honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        ∀ op, runCountB S guest (honest coreProgram fs H C hdr T) op n Regs.initial ≤ cnt T op := by
  intro hdr rd T hname hH n hn op
  obtain ⟨c, hc, hle⟩ := mainB_runC h hname hH
  have hjt : JumpTables (honest coreProgram fs H C hdr T) :=
    jumpTablesB_honestC hH.toHonestB hname
  have hpro := runCB_jumpTables (S := S) hjt
  rw [show (⟨gpow 0, 1⟩ : Regs K) = Regs.initial by rw [gpow, pow_zero]; rfl] at hpro
  rw [countB_eq_of_runC (hpro.trans hc) hn op, Pi.add_apply]
  have := hle op
  unfold cnt
  omega


/-! ## At the deployed semantics -/

section Deployed

/-- At the deployed semantics, `InstRunsB` is `B2.lean`'s `InstRuns`. -/
theorem instRunsB_deployed {κ : ℕ} (L : MemImage κ) (I : Inst) (args rets : List E) :
    InstRunsB blakeDeployed L I args rets = InstRuns L I args rets := by
  simp only [InstRunsB, InstRuns, runCB_deployed]

/-- **At the deployed semantics, `B2HypsB` is `B2.lean`'s `B2Hyps`.** -/
theorem b2HypsB_deployed : B2HypsB blakeDeployed = B2Hyps := by
  apply propext
  constructor <;> intro h <;> cases h <;> constructor <;>
    first | assumption | (simp only [cplRunB_deployed, honestAtB_deployed] at *; assumption)

end Deployed

end
end LeanVM.Guest.B2C
