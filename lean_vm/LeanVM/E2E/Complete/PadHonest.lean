/-
  LeanVM.E2E.Complete.PadHonest

  T6, recursion: what the decoding of an honest node's children (D3) reads of the honest memory
  holds of the memory zero-padded: the facts transport along a memory extension.
-/

module

public import LeanVM.E2E.Complete.HonestBodies
public import LeanVM.E2E.Complete.Rom.Pad

/-!
# The honest memory, zero-padded

leanVM's prover pads the memory of a run with zero cells until its stack reaches the aggregation's
floor of 22 variables (`Rom/Pad.lean`). The honest memory `honest … T` has `2^logMem (total)`
words; its padding `padImage κ' (honest … T)`, for `κ'` between that and `32`, extends it
(`MemExt`): every read of the honest memory reads the same word, and every read with the default
`0` (the decoder's `wd`, `cellAt`) is unchanged.

Every fact the decoding of the children (D3, `DecodeFinal.lean`) consumes of the honest memory
reads it positively (a read giving a word), so it holds of any extension:

* the runs (`ReachB`, `SafeB`, `RunCB` with their counts, `retRegs`, `OnRunB`, `InstRunsB`) and
  their `BLAKE2S` rows (`runRows_of_ext`, so the run's table semantics `honestSem` is one);
* the frames' cells (`B2C.FrameHolds`), the jump tables, the environment, the bounds, the bounded
  memory and the exponent tables (`SemHolds`, at `B1.ExpTables`, a list of loads);
* the evaluations (`Tree.ValidB`, by its equations' reads, `Tree.ValidB.transfer`);
* the decoder's valuations (`wd`, `valG`, `Located.valAt`, `frameWords`), equal.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Value
open LeanVM.Guest.Exec (EnvHolds Sym)

@[expose] public section

/-! ## Extensions -/

/-- **`L'` extends `L`**: every read of `L` reads the same word in `L'`, and the reads with the
default `0` agree. -/
structure MemExt {κ κ' : ℕ} (L : MemImage κ) (L' : MemImage κ') : Prop where
  /-- A read of `L` reads alike. -/
  read : ∀ a v, L.read a = some v → L'.read a = some v
  /-- The reads with the default `0` agree. -/
  getD : ∀ a, (L'.read a).getD 0 = (L.read a).getD 0

theorem memExt_refl {κ : ℕ} (L : MemImage κ) : MemExt L L := ⟨fun _ _ h ↦ h, fun _ ↦ rfl⟩

/-- **The zero padding extends the memory.** -/
theorem memExt_padImage {κ κ' : ℕ} (hκ' : κ' < 64) (hle : κ ≤ κ') (L : MemImage κ) :
    MemExt L (padImage κ' L) :=
  ⟨fun _ _ h ↦ padImage_read_of hκ' hle h, padImage_read_getD hκ' hle L⟩

variable {κ κ' : ℕ} {L : MemImage κ} {L' : MemImage κ'}

/-! ## The decoder's valuations -/

theorem MemExt.wd (h : MemExt L L') (fp : K) (o : ℕ) : Check.wd L' fp o = Check.wd L fp o := by
  simp only [Check.wd, h.getD]

theorem MemExt.valG (h : MemExt L L') (fp : K) (C : Check.Cert) :
    Check.valG L' fp C = Check.valG L fp C := by
  funext v
  exact h.wd fp _

theorem MemExt.valAt (h : MemExt L L') (f : String) (a : ℕ) :
    Located.valAt L' f a = Located.valAt L f a := by
  unfold Located.valAt frameVal
  exact h.valG _ _

theorem MemExt.frameWords (h : MemExt L L') (fp : K) (o n : ℕ) :
    Check.frameWords L' fp o n = Check.frameWords L fp o n := by
  simp only [Check.frameWords, h.wd]

/-! ## Runs -/

theorem MemExt.reachB (h : MemExt L L') {S : BlakeSem} {prog : Semantics.Program} {s t : Regs K}
    (hr : ReachB S prog L s t) : ReachB S prog L' s t := by
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, runB_of_ext h.read n hn⟩

theorem MemExt.safeB (h : MemExt L L') {S : BlakeSem} {prog : Semantics.Program} {k : ℕ} {r : Regs K}
    (hs : SafeB S prog L k r) : SafeB S prog L' k r :=
  runB_of_ext h.read k hs

/-- **The counts of a run are its counts on any extension** (`B2C.runCountB`). -/
theorem b2cRunCountB_of_ext {S : BlakeSem} {prog : Semantics.Program}
    (hrd : ∀ a v, L.read a = some v → L'.read a = some v) (op : Opcode) :
    ∀ (n : ℕ) {r r2 : Regs K}, runB S prog L n r = some r2 →
      B2C.runCountB S prog L' op n r = B2C.runCountB S prog L op n r
  | 0, r, r2, _ => rfl
  | n + 1, r, r2, h => by
    unfold runB at h
    split_ifs at h with hf
    obtain ⟨r1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have h1' := stepB_of_ext hrd h1
    unfold B2C.runCountB
    obtain ⟨i, hi, -⟩ := Option.bind_eq_some_iff.mp h1
    rw [hi, h1, h1']
    dsimp only
    rw [b2cRunCountB_of_ext hrd op n h2]

theorem MemExt.runCB (h : MemExt L L') {S : BlakeSem} {prog : Semantics.Program} {s t : Regs K}
    {c : Opcode → ℕ} (hr : B2C.RunCB S prog L s t c) : B2C.RunCB S prog L' s t c := by
  obtain ⟨n, hn, hc⟩ := hr
  exact ⟨n, runB_of_ext h.read n hn, fun op ↦ (b2cRunCountB_of_ext h.read op n hn).trans (hc op)⟩

theorem MemExt.retRegs (h : MemExt L L') {fp : K} {r : Regs K}
    (hr : Guest.retRegs L fp = some r) : Guest.retRegs L' fp = some r := by
  unfold Guest.retRegs at hr ⊢
  obtain ⟨d, hd, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hr
  rw [h.read _ _ hd, Option.bind_some, h.read _ _ hf, Option.map_some]

theorem MemExt.onRunB (h : MemExt L L') {S : BlakeSem} {I : Inst} (ho : B2C.OnRunB S L I) :
    B2C.OnRunB S L' I := by
  obtain ⟨h1, r, hr, h2, h3⟩ := ho
  refine ⟨h.reachB h1, r, ?_, h.reachB h2, h.reachB h3⟩
  split_ifs at hr ⊢
  · exact hr
  · exact h.retRegs hr

theorem MemExt.instRunsB (h : MemExt L L') {S : BlakeSem} {I : Inst} {args rets : List E}
    (hi : B2C.InstRunsB S L I args rets) : B2C.InstRunsB S L' I args rets := by
  obtain ⟨r, c, hr, hc, hw, hrets⟩ := hi
  refine ⟨r, c, ?_, h.runCB hc, hw, fun k hk ↦ h.read _ _ (hrets k hk)⟩
  split_ifs at hr ⊢
  · exact hr
  · exact h.retRegs hr

/-- A `BLAKE2S` instruction that executes reads the same row on an extension. -/
theorem blakeRowAt_of_ext {S : BlakeSem} {rd rd2 : K → Option E}
    (hrd : ∀ a v, rd a = some v → rd2 a = some v) {r r2 : Regs K} {i : Instr}
    (he : executeWithB S rd r i = some r2) : blakeRowAt rd2 r i = blakeRowAt rd r i := by
  cases i with
  | blake2s om ocv oout omd =>
    simp only [executeWithB, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, c0, h4, c1, h5, o0, h6, o1, h7, md, h8, -⟩ := he
    simp only [blakeRowAt, Option.bind_eq_bind, h0, h1, h2, h3, h4, h5, h6, h7, h8, hrd _ _ h0,
      hrd _ _ h1, hrd _ _ h2, hrd _ _ h3, hrd _ _ h4, hrd _ _ h5, hrd _ _ h6, hrd _ _ h7, hrd _ _ h8,
      Option.bind_some]
  | _ => rfl

/-- **A run's `BLAKE2S` rows are its rows on any extension.** -/
theorem runRows_of_ext {S : BlakeSem} {prog : Semantics.Program}
    (hrd : ∀ a v, L.read a = some v → L'.read a = some v) :
    ∀ (n : ℕ) {r rf : Regs K}, runB S prog L n r = some rf →
      runRows S prog L' n r = runRows S prog L n r
  | 0, _, _, _ => rfl
  | n + 1, r, rf, hr => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runB, hpc] at hr
    simp only [runB, hpc, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨r', hs, hrun⟩ := hr
    obtain ⟨i, hf, he⟩ := Option.bind_eq_some_iff.mp hs
    have hs' : stepB S prog L' r = some r' := stepB_of_ext hrd hs
    rw [runRows_succ hpc hf hs, runRows_succ hpc hf hs', runRows_of_ext hrd n hrun,
      blakeRowAt_of_ext hrd he]

/-- **The rows V_I lists of a run, on an extension**, under the Flock-blind semantics. -/
theorem blakeRows_of_ext {S : BlakeSem} (hS : ∀ b, S.row b → blakeFree.row b) {prog : Semantics.Program}
    (hrd : ∀ a v, L.read a = some v → L'.read a = some v) {n : ℕ} {rf : Regs K}
    (hr : runB S prog L n Regs.initial = some rf) :
    Trace.blakeRows blakeFree (⟨κ', L', n⟩ : Trace prog) =
      Trace.blakeRows blakeFree (⟨κ, L, n⟩ : Trace prog) := by
  unfold Trace.blakeRows
  dsimp only
  rw [runRows_eq_of_runB hS (runB_of_ext hrd n hr), runRows_of_ext hrd n hr,
    runRows_eq_of_runB hS hr]

/-! ## Frames and preconditions -/

theorem MemExt.frameHolds (h : MemExt L L') {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
    {kfps : List ℕ} {hdr : E × E} (hF : B2C.FrameHolds L j fp σ es vs kfps hdr) :
    B2C.FrameHolds L' j fp σ es vs kfps hdr where
  hdr0 := h.read _ _ hF.hdr0
  hdr1 := h.read _ _ hF.hdr1
  hdrK := hF.hdrK
  val v hv h2 h3 := h.read _ _ (hF.val v hv h2 h3)
  tmp e he t ht h2 h3 := h.read _ _ (hF.tmp e he t ht h2 h3)
  stat p hp h2 h3 := h.read _ _ (hF.stat p hp h2 h3)
  addr := hF.addr
  arm a ha h2 h3 := h.read _ _ (hF.arm a ha h2 h3)
  len := hF.len
  site i c kfp s h1 h2 h3 := ⟨fun a b ↦ h.read _ _ ((hF.site i c kfp s h1 h2 h3).1 a b),
    fun a b c' ↦ h.read _ _ ((hF.site i c kfp s h1 h2 h3).2 a b c')⟩
  kid i c kfp h1 h2 := ⟨h.read _ _ (hF.kid i c kfp h1 h2).1, h.read _ _ (hF.kid i c kfp h1 h2).2.1,
    fun k hk ↦ h.read _ _ ((hF.kid i c kfp h1 h2).2.2.1 k hk),
    fun o ho ↦ h.read _ _ ((hF.kid i c kfp h1 h2).2.2.2 o ho)⟩
  tail := hF.tail

theorem MemExt.jumpTables (h : MemExt L L') (hj : End.JumpTables L) : End.JumpTables L' :=
  fun q hq ↦ h.read _ _ (hj q hq)

theorem MemExt.envHolds (h : MemExt L L') {fp : K} {env : Exec.Trie Sym}
    (he : EnvHolds L fp env) : EnvHolds L' fp env :=
  fun n v hv ↦ h.read _ _ (he n v hv)

theorem MemExt.bndHolds (h : MemExt L L') {fp : K} {bnd : List (ℕ × ℕ)}
    (hb : BndHolds L fp bnd) : BndHolds L' fp bnd := fun p hp ↦ by
  obtain ⟨e, he, hr⟩ := hb p hp
  exact ⟨e, he, h.read _ _ hr⟩

theorem MemExt.memPre (h : MemExt L L') {fp : K} {mem : List (ℕ × ℕ × ℕ)}
    (hm : MemPre L fp mem) : MemPre L' fp mem := fun m hm' c hc ↦ by
  obtain ⟨p, hp, hk, e, he, hr⟩ := hm m hm' c hc
  exact ⟨p, h.read _ _ hp, hk, e, he, h.read _ _ hr⟩

theorem MemExt.loadHolds (h : MemExt L L') {p : E} {off : ℕ} {d : E}
    (hl : LoadHolds L.read p off d) : LoadHolds L'.read p off d :=
  ⟨hl.1, h.read _ _ hl.2⟩

/-- **The exponent tables' relation** (`glob`'s semantic pairs) holds on an extension. -/
theorem MemExt.semHolds (h : MemExt L L') {fp : K} {sems : List (ℕ × ℕ)}
    (hs : SemHolds glob L fp sems) : SemHolds glob L' fp sems := fun p hp ↦ by
  have := hs p hp
  show B1.ExpTables L'.read (Check.wd L' fp p.1) (Check.wd L' fp p.2)
  rw [h.wd, h.wd]
  exact fun j hj ↦ ⟨h.loadHolds (this j hj).1, h.loadHolds (this j hj).2⟩

/-! ## Evaluations -/

/-- **An evaluation valid on `L`, its equations read there, is valid on an extension.** -/
theorem MemExt.validB (h : MemExt L L') {S : BlakeSem} {P : Core.Program} {t : Tree}
    {args rets : List E} (hv : t.ValidB S P L.read args rets)
    (he : ∀ q ∈ t.eqns P, L.read q.1 = some q.2) : t.ValidB S P L'.read args rets :=
  Tree.ValidB.transfer t hv fun q hq ↦ h.read _ _ (he q hq)

end
end LeanVM.E2E.Complete
