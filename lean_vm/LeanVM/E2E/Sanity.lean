/-
  LeanVM.E2E.Sanity

  The sanity theorem of the end-to-end security statement (T7′ of `docs/roadmap/e2e-security.md`):
  on what the deployed verifier accepts, the idealized verifier V_I with BLAKE2s accepts, given
  the words of the reached commitments, the full leanISA relation of the reached candidates, the
  precheck of their tables and enough fuel.
-/

module

public import LeanVM.E2E.Guest
public import LeanVM.E2E.Complete.Node
public import LeanVM.E2E.Complete.Table
public import LeanVM.Protocol.EndToEnd.Execution
public import LeanVM.Guest.Value.NodeSome
public import Mathlib.Data.Set.Finite.List

/-!
# V_I accepts what the deployed system accepts (T7′)

The design's T7′: deployed checks accept, the idealized proof's words cover every reached root,
every reached candidate satisfying the relation without Flock satisfies the full one, the
precheck holds, V_I's cost is within its budget ⇒ V_I with BLAKE2s accepts. Here V_I runs in `Id`
with `blake2sBytes` (`blakeId`), and the deployed checks are the outer verifier's
(`Node.verifyAggregate guest s ip.proof`).

**The statement** (`idealVerify_blake2s`). Of the nodes V_I reaches (`Reached`: the root, and the
children a reached node's step returns), four hypotheses, each a fact the deployed checks do not
give:

* `WordsCover`: the idealized proof gives each reached node a well-shaped word whose BLAKE2s
  Merkle root is the node's stack root (the deployed proof opens the commitment at a few columns
  only);
* `CandidatesAux`: every candidate V_I follows (a stack within level 0's Johnson radius of the
  word satisfying `M3HoldsBlind`) satisfies Flock's R1CS (`aux`), so the full `M3Holds` (V_I
  follows every candidate in the list, not only the one an extractor would find);
* `TablesPrecheck`: no two active non-final `BLAKE2S` rows of a reached candidate's run with
  distinct inputs have equal outputs (a BLAKE2s compression collision);
* `FuelBounds`: a size of nodes, at most the fuel at the root, exceeding the total size of each
  reached node's children (the closure terminates within its steps; under BLAKE2s a cycle of
  nodes is a hash fixed point, not excluded).

No hypothesis is on the frames the idealized proof names (E2E-5): T2 holds at every frame
chooser (`guest_knowledge_model_all`), so the theorem holds for every `ip.frames`.

**What is discharged.**

* The root: V° accepts the deployed verifier's accepted proof (`verifyBlind_of_verify`), the outer
  checks pass (`outerChecksWith_true`: the DA vector digests by `vectorDigestOfWith_id`, the
  bytecode part by `bytecodeHolds_of_holds`).
* The head of every reached node (`Head`, `head_of_runProof`): a proof the verifier's execution
  check accepts, with any values of the fixed polynomials and any answered hash, announces sizes
  whose layout is the verifier's at admissible sizes (`good_of_readSizes`, so `sizesOf` is
  defined), a stack root (`xrun_commitStack`) and a commitment of level 0's shape
  (`exists_ladder`). The root's proof is the deployed verifier's (`runProof_some`).
* A candidate's run (`candidateRun_of_m3Holds`): the full relation gives a deployed execution
  (`execution_of_extracted`), which is the halting Flock-blind run V_I re-runs
  (`haltingRunB_of_validB`).
* Its table (`tableOKWith_run`): its rows are rows of the compression function
  (`blakeRows_deployed`), so every standard chain ends at `blake2sBytes`
  (`stdChain_out_eq_blake2sBytes`); with the precheck V_I's table check accepts once finitely
  many strings have a standard chain among the rows. That is proved, not assumed
  (`chainInputs_finite_of_card`): the non-final rows of a chain carry the counters
  `64, 128, …`, distinct below `2^64`, and the metadata cells are memory words
  (`md_mem_range_of_mem_runRows`), at most `2^32` distinct ones, so a chain has at most
  `2^32 + 1` rows.
* Its children have heads (`head_of_child`): the execution is valid under its own table
  (`validExecutionB_tableSem_iff`), which passes the table check at BLAKE2s
  (`tableOK_blake2s`); T2 at the table's model with the hash `some ∘ blake2sBytes`
  (`tableModel`, `HashModel.oracle` at any answered hash) has every child decoded at V_I's
  decoder, at any frames, accepted by the deferring verifier with BLAKE2s, so with a head.
* The closure (`closure_accepts`) over the reached nodes with heads, each stepping to children
  with heads (`step_of_reached`, `nodeStep_eq_some`), within the fuel.
-/

namespace LeanVM.E2E.Sanity

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Compile.Rom
open LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-! ## The head of an accepted proof -/

/-- **What V_I reads of a node's proof first** (`nodeStep`): the announced layout and rate, the
sizes they give, the stack's root, and the shape of the stack's commitment. -/
structure Head (prog : Program) (π : Proof) where
  /-- The announced layout. -/
  layout : Verifier.Layout
  /-- The announced rate. -/
  rate : ℕ
  /-- The sizes of the layout. -/
  sizes : Sizes
  /-- The stack's root. -/
  root : E × E
  /-- The height of the stack's commitment. -/
  height : ℕ
  /-- The width of the stack's commitment. -/
  width : ℕ
  /-- The layout and rate are announced. -/
  announced_eq : Verifier.announced (bytecodeWords prog) π.stream = some (layout, rate)
  /-- The sizes are the layout's. -/
  sizes_eq : sizesOf prog layout = some sizes
  /-- The root is announced. -/
  root_eq : stackRoot π = some root
  /-- The commitment has that shape. -/
  shape_eq : stackShape layout rate = some (height, width)

/-- The sizes `sizesOf` reads off a layout are admissible. -/
theorem admissible_of_sizesOf {prog : Program} {layout : Verifier.Layout} {s : Sizes}
    (h : sizesOf prog layout = some s) : s.Admissible prog := by
  unfold sizesOf at h
  split at h
  · rename_i hex
    obtain rfl := Option.some.inj h
    exact hex.choose_spec.2
  · simp at h

/-- The verifier's execution check starts with the announced sizes, then the stack's
commitment. -/
theorem verifyExecution_eq (ev : Evaluations) (bytecode : List K) (pi : Digest) :
    ∃ k : Verifier.Layout × ℕ → Prog Unit, verifyExecution ev bytecode pi =
      (readSizes bytecode).bind fun a ↦ (commitStack a.1.stackLog a.2).bind fun _ ↦ k a :=
  ⟨_, rfl⟩

/-- **An accepted proof has a head**: a proof the verifier's execution check accepts, with any
values of the fixed polynomials and every hash answered by `H`, announces sizes and a rate whose
layout is the verifier's at admissible sizes, a stack root, and a commitment of level 0's
shape. -/
theorem head_of_runProof {H : Bytes → Option Digest} {prog : Program} {ev : Evaluations}
    {pi seed : Digest} {π : Proof}
    (h : runProof H (verifyExecution ev (bytecodeWords prog) pi >>= fun _ ↦ pure true) seed π =
      some true) : Nonempty (Head prog π) := by
  simp only [runProof, bind, Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, h⟩ := h
  rcases r with _ | ⟨_ | _, s⟩
  · simp [pure] at h
  · simp [pure] at h
  obtain ⟨hist, hx⟩ := xrun_of_run H _ _ [] hr
  rw [xrun_bind, Option.bind_eq_some_iff] at hx
  obtain ⟨⟨u, s₂, h₂⟩, hve, -⟩ := hx
  obtain ⟨k, hk⟩ := verifyExecution_eq ev (bytecodeWords prog) pi
  rw [hk, xrun_bind, Option.bind_eq_some_iff] at hve
  obtain ⟨⟨⟨layout, ρ⟩, s₁, h₁⟩, hrs, hbody⟩ := hve
  rw [xrun_bind, Option.bind_eq_some_iff] at hbody
  obtain ⟨⟨u', s₃, h₃⟩, hcs, -⟩ := hbody
  obtain ⟨xs, hxl, hstream, -, -, hrun⟩ :=
    xrun_of_readsN H (readsN_readSizes (bytecodeWords prog)) hrs
  have hann : Verifier.announced (bytecodeWords prog) π.stream = some (layout, ρ) :=
    hrun (fun _ ↦ pure default) default [] []
  obtain ⟨l₁, -, hl₁, -⟩ := xrun_after H _ _ _ hrs
  obtain ⟨g, hg, hadm, hwa, -⟩ := good_of_readSizes prog hl₁
  obtain ⟨sz, hsz⟩ : ∃ sz, sizesOf prog layout = some sz := by
    unfold sizesOf
    split
    · exact ⟨_, rfl⟩
    · rename_i hn
      exact absurd ⟨g, hg.symm, hadm⟩ hn
  obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hwa
  obtain ⟨x0, x1, xs', root', hs₁, -, -⟩ := xrun_commitStack H hc hcs
  simp only at hstream
  rw [hs₁] at hstream
  have hroot : stackRoot π = some (x0, x1) := by
    have h2 : (xs ++ x0 :: x1 :: xs')[2 + tables.length]? = some x0 := by
      rw [List.getElem?_append_right (by omega)]; simp [hxl]
    have h3 : (xs ++ x0 :: x1 :: xs')[3 + tables.length]? = some x1 := by
      rw [List.getElem?_append_right (by omega)]
      rw [show 3 + tables.length - xs.length = 1 by omega]; rfl
    unfold stackRoot
    rw [hstream, h2, h3]
    rfl
  have hshape : stackShape layout ρ = some (levelShape layout.stackLog ⟨laneBits, ρ, q₀⟩
      (2 ^ (⟨laneBits, ρ, q₀⟩ : Whir.Level).fold)) := by
    unfold stackShape
    rw [hc]
  exact ⟨⟨layout, ρ, _, (x0, x1), _, _, hann, hsz, hroot, hshape⟩⟩

/-! ## The candidates' runs -/

/-- **A candidate satisfying the full relation runs**: at admissible sizes, a stack satisfying the
leanISA relation reads back to a valid execution of the guest (`execution_of_extracted`), the one
V_I re-runs under the Flock-blind semantics (`candidateRun`). -/
theorem candidateRun_of_m3Holds {s : Sizes} (hs : s.Admissible Guest.guest) {input : PublicInput}
    {q : Column (leanIsaμ Guest.guest s)}
    (h : M3Holds (leanIsaInstance F₀ Guest.guest s) input q) :
    ∃ t, candidateRun Guest.guest s q = some t ∧ ValidExecution Guest.guest input t := by
  obtain ⟨t, hrep, hv⟩ := execution_of_extracted F₀ Guest.guest_sentinelSafe hs h
  have hrun := haltingRunB_of_validB (S := blakeDeployed)
    (fun _ hb ↦ canonicalCells_of_compressCells hb)
    ((validExecutionB_deployed _ _ _).mpr hv)
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  unfold candidateRun
  generalize Arithmetization.imageOf (witnessOf F₀ Guest.guest s q).data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  exact ⟨_, hrun, hv⟩

/-! ## The table check at BLAKE2s -/

/-- The metadata cell of a row a step reads is a word of the memory. -/
theorem md_mem_of_blakeRowAt {κ : ℕ} {L : MemImage κ} {r : Regs K} {i : Instr} {b : BlakeRow}
    (h : blakeRowAt L.read r i = some b) : b.md ∈ Set.range L := by
  cases i with
  | blake2s om ocv oout omd =>
    simp only [blakeRowAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨m0, -, m1, -, m2, -, m3, -, cv0, -, cv1, -, o0, -, o1, -, md, hmd, hb⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at hb
    subst hb
    simp only [MemImage.read, Option.map_eq_some_iff] at hmd
    obtain ⟨j, -, hj⟩ := hmd
    exact ⟨j, hj⟩
  | _ => simp [blakeRowAt] at h

/-- **The metadata cells of a run's rows are words of the memory.** -/
theorem md_mem_range_of_mem_runRows {S : BlakeSem} {κ : ℕ} {prog : Program} {L : MemImage κ} :
    ∀ {n : ℕ} {r : Regs K} {b : BlakeRow}, b ∈ runRows S prog L n r → b.md ∈ Set.range L
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, r, b, h => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runRows, hpc] at h
    cases hf : prog.fetch r.pc with
    | none => simp [runRows, hpc, hf] at h
    | some i =>
      cases hs : stepB S prog L r with
      | none => simp [runRows, hpc, hf, hs] at h
      | some r' =>
        rw [runRows_succ hpc hf hs] at h
        rcases List.mem_append.mp h with h | h
        · exact md_mem_of_blakeRowAt (Option.mem_toList.mp h)
        · exact md_mem_range_of_mem_runRows h

/-- Rows whose metadata cells are words of a memory of `2^κ` words have at most `2^κ` distinct
metadata cells. -/
theorem card_md_le {κ : ℕ} (L : MemImage κ) {rows : List BlakeRow}
    (h : ∀ b ∈ rows, b.md ∈ Set.range L) : (rows.map (·.md)).toFinset.card ≤ 2 ^ κ := by
  classical
  calc (rows.map (·.md)).toFinset.card ≤ (Finset.univ.image L).card :=
        Finset.card_le_card fun e he ↦ by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
          obtain ⟨i, hi⟩ := h b hb
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    _ ≤ (Finset.univ : Finset (Fin (2 ^ κ))).card := Finset.card_image_le
    _ = 2 ^ κ := by simp

/-- **A standard chain among rows of few metadata cells is short**: its non-final rows carry the
counters `64, 128, …`, distinct below `2^64`, so it has at most one row more than the `N < 2^57`
distinct metadata cells of the rows. -/
theorem length_le_of_stdChain {rows : List BlakeRow} {N : ℕ} (hN : N < 2 ^ 57)
    (hcard : (rows.map (·.md)).toFinset.card ≤ N) {x : List UInt8} {c : List BlakeRow}
    (hsub : ∀ r ∈ c, r ∈ rows) (hs : StdChain x c) : c.length ≤ N + 1 := by
  by_contra hlt
  have hinj : Set.InjOn (fun i : Fin (N + 1) ↦ (c[i.val]'(by omega)).md)
      (Finset.univ : Finset (Fin (N + 1))) := by
    intro i _ j _ hij
    have hi := (hs.2.2.1 i.val (by omega)).2
    have hj := (hs.2.2.1 j.val (by omega)).2
    simp only at hij
    rw [hij] at hi
    have e := congrArg (fun t ↦ t.1.toNat) (hi.symm.trans hj)
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at e
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
    exact Fin.ext (by omega)
  have := Finset.card_le_card_of_injOn _ (fun i _ ↦ List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨_, hsub _ (List.getElem_mem _), rfl⟩)) hinj
  have h2 := le_trans this hcard
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- **Finitely many strings have a standard chain** among rows of fewer than `2^57` distinct
metadata cells. -/
theorem chainInputs_finite_of_card {rows : List BlakeRow} {N : ℕ} (hN : N < 2 ^ 57)
    (hcard : (rows.map (·.md)).toFinset.card ≤ N) : (chainInputs rows).Finite := by
  refine (List.finite_length_le UInt8 (64 * (N + 1))).subset ?_
  rintro x ⟨c, -, hsub, hs⟩
  have hc := length_le_of_stdChain hN hcard hsub hs
  have h1 := hs.1
  show x.length ≤ 64 * (N + 1)
  omega

/-- **V_I's table check accepts rows of the compression function** that pass the precheck, when
finitely many strings have a standard chain among them. -/
theorem tableOKWith_blake2s {rows : List BlakeRow} (hd : ∀ b ∈ rows, blakeDeployed.row b)
    (hpre : Precheck rows) (hfin : (chainInputs rows).Finite) :
    tableOKWith (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest)) rows = true := by
  unfold tableOKWith
  simp only [hpre, hfin, ↓reduceIte, ↓reduceDIte]
  refine allM_id_true _ _ fun x _ ↦ ?_
  classical
  exact decide_eq_true fun c hc hsub hs ↦
    stdChain_out_eq_blake2sBytes hs (fun r hr ↦ hd r (hsub r hr)) hc

/-- The rows of a deployed execution, as V_I lists them under the Flock-blind semantics, are rows
of the compression function. -/
theorem blakeRows_deployed {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) : ∀ b ∈ t.blakeRows blakeFree, blakeDeployed.row b :=
  blakeRows_of_validB (S := blakeDeployed) (fun _ hb ↦ canonicalCells_of_compressCells hb)
    ((validExecutionB_deployed _ _ _).mpr hv)

/-- **V_I's table check accepts a deployed execution's rows** that pass the precheck: they are
rows of the compression function (`blakeRows_deployed`), in a memory of at most `2^32` words, so
finitely many strings have a standard chain among them. -/
theorem tableOKWith_run {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hpre : Precheck (t.blakeRows blakeFree)) :
    tableOKWith (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest))
      (t.blakeRows blakeFree) = true := by
  refine tableOKWith_blake2s (blakeRows_deployed hv) hpre
    (chainInputs_finite_of_card (N := 2 ^ t.κ) ?_
      (card_md_le t.image fun b hb ↦ md_mem_range_of_mem_runRows hb))
  have h32 : t.κ ≤ 32 := hv.1.2.1
  calc 2 ^ t.κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) h32
    _ < 2 ^ 57 := by norm_num

/-! ## The children a candidate decodes -/

/-- **The last row of a prefix** gives `H`'s answer for the whole string, when the table passes
the check at `H` (`tablePrefix_final` at any answered hash). -/
theorem tablePrefix_final_of {rows : List BlakeRow} {H : Bytes → Option Digest}
    (h : TableOK H rows) {bs : List (List UInt8)} {st : E × E} {m : Fin 4 → E} {r : List UInt8}
    {out0 out1 : E} (hp : TablePrefix rows bs st) (hr : r.length ≤ 64) (hr' : bs = [] ∨ r ≠ [])
    (hm : blockBytes m = r ++ List.replicate (64 - r.length) 0)
    (hc : (tableSem rows).check m st.1 st.2 out0 out1
      (metadataCell (64 * bs.length + r.length) true)) :
    ∃ d, H (bs.flatten ++ r) = some d ∧ (out0, out1) = digestScalars d := by
  obtain ⟨c, hrows, hc', rfl⟩ := hp
  obtain ⟨hcan, hmem⟩ := hc
  have hs := stdChain_snoc hc' (b := ⟨m, (chainState c).1, (chainState c).2, out0, out1,
    metadataCell (64 * bs.length + r.length) true⟩) rfl hr hr' hm rfl
  have hrows' : ∀ b ∈ c ++ [⟨m, (chainState c).1, (chainState c).2, out0, out1,
      metadataCell (64 * bs.length + r.length) true⟩], b ∈ rows := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hrows b hb
    · exact List.mem_singleton.mp hb ▸ hmem
  have := h _ _ (by simp) hrows' hs
  rw [List.getElem_concat_length (by simp)] at this
  exact ⟨_, this, pair_eq_digestScalars_iff.mpr ⟨hcan.2.2.2.1, hcan.2.2.2.2.1, rfl⟩⟩

/-- **The table model at a hash**: the table's semantics, every string answered by `H`, when the
table passes the check at `H` (`HashModel.oracle` at any answered hash). -/
noncomputable def tableModel (rows : List BlakeRow) (H : Bytes → Option Digest)
    (h : TableOK H rows) : HashModel where
  sem := tableSem rows
  canonical hc := hc.1
  H := H
  Prefix := TablePrefix rows
  prefix_nil := tablePrefix_nil rows
  prefix_step := tablePrefix_step
  final := tablePrefix_final_of h

/-- **The children a deployed execution decodes have heads**, at every frame chooser: the
execution is valid under its own table, which passes the check at BLAKE2s, so T2 at that model
(`guest_knowledge_model_all`) has every decoded child's proof accepted by the deferring
verifier with BLAKE2s, and an accepted proof has a head (`head_of_runProof`). -/
theorem head_of_child {input : PublicInput} {t : Trace Guest.guest}
    (hv : ValidExecution Guest.guest input t) (fr : String → List E → Option ℕ) {c : Node.Child}
    (hc : c ∈ (Guest.End.decodeAt (tableSem (t.blakeRows blakeFree)) fr t.image).witness.children) :
    Nonempty (Head Guest.guest c.proof) := by
  have hok : TableOK someBlake (t.blakeRows blakeFree) := tableOK_blake2s (blakeRows_deployed hv)
  have hvt : ValidExecutionB (tableSem (t.blakeRows blakeFree)) Guest.guest input t :=
    (validExecutionB_tableSem_iff _ _ _).mpr (validExecutionB_blakeFree_of_valid hv)
  obtain ⟨-, -, hkids, -⟩ := guest_knowledge_model_all (tableModel _ someBlake hok) fr input t hvt
  obtain ⟨-, pi, -, hver⟩ := hkids c hc
  simp only [verifyDeferredWith, bind, Option.bind_eq_some_iff] at hver
  obtain ⟨sd, -, hrun⟩ := hver
  exact head_of_runProof (ev := .claimed c.fresh) hrun

/-! ## V_I's step on a node -/

/-- **The candidates' loop of `nodeStep`, in `Id`**: when every element, from any children
satisfying `Q`, steps on to children satisfying `Q`, the loop ends without an exit, with
children satisfying `Q`. -/
theorem forIn_yield_id {α γ : Type} (L : List α)
    (F : α → Option γ × List Node → Id (ForInStep (Option γ × List Node)))
    (Q : List Node → Prop)
    (hF : ∀ a ∈ L, ∀ k, Q k → ∃ k', F a (none, k) = ForInStep.yield (none, k') ∧ Q k') :
    ∀ k0, Q k0 → (forIn L (none, k0) F).1 = none ∧ Q (forIn L (none, k0) F).2 := by
  induction L with
  | nil => intro k0 hk0; exact ⟨rfl, hk0⟩
  | cons a L ih =>
    intro k0 hk0
    obtain ⟨k', hstep, hk'⟩ := hF a List.mem_cons_self k0 hk0
    rw [List.forIn_cons, hstep]
    exact ih (fun b hb k hk ↦ hF b (List.mem_cons_of_mem a hb) k hk) k' hk'

/-- **The candidates' loop of `nodeStep` and what follows it, in `Id`**: when every element
steps on as in `forIn_yield_id`, and the continuation returns children satisfying `Q` on any
exit-free state with children satisfying `Q`, the whole returns such children. -/
theorem forIn_bind_yield_id {α γ : Type} (L : List α)
    (F : α → Option γ × List Node → Id (ForInStep (Option γ × List Node)))
    (Q : List Node → Prop)
    (hF : ∀ a ∈ L, ∀ k, Q k → ∃ k', F a (none, k) = ForInStep.yield (none, k') ∧ Q k')
    (hQ : Q []) (G : Option γ × List Node → Id (Option (List Node)))
    (hG : ∀ k, Q k → ∃ kids, Id.run (G (none, k)) = some kids ∧ Q kids) :
    ∃ kids, Id.run (forIn L (none, []) F >>= G) = some kids ∧ Q kids := by
  obtain ⟨h1, h2⟩ := forIn_yield_id L F Q hF [] hQ
  rw [Id.run_bind]
  generalize forIn L (none, []) F = st at h1 h2
  obtain ⟨r, k⟩ := st
  simp only at h1 h2
  subst h1
  exact hG k h2

/-- **V_I's step on a node with a head**, with BLAKE2s: when the idealized proof gives the node a
well-shaped word with its stack root, and every candidate runs, passes the table check and decodes
children whose proofs satisfy `Good`, the step returns children whose proofs satisfy `Good`. -/
theorem nodeStep_eq_some {prog : Program} {seed : Digest} {ip : IdealProof} {pi : Digest}
    {π : Proof} (hd : Head prog π) {W : Word} (hW : ip.word (pi, π) = some W)
    (hws : WellShaped hd.width W)
    (hr : digestScalars (treeRoot blake2sBytes hd.height W) = hd.root)
    (Good : Proof → Prop)
    (hq : ∀ q ∈ blindCandidates prog hd.sizes hd.rate pi W, ∃ t,
      candidateRun prog hd.sizes q = some t ∧
      tableOKWith (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest))
        (t.blakeRows blakeFree) = true ∧
      ∀ c ∈ (Guest.End.decodeAt (tableSem (t.blakeRows blakeFree)) (ip.frames (pi, π))
        t.image).witness.children, Good c.proof) :
    ∃ kids, nodeStep (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest)) prog seed ip
      (pi, π) = some kids ∧ ∀ κ ∈ kids, Good κ.2 := by
  have hfin : (blindCandidates prog hd.sizes hd.rate pi W).Finite := Set.toFinite _
  have hroot : treeRoot (fun x ↦ (pure (blake2sBytes x) : Id Digest)) hd.height W =
      treeRoot blake2sBytes hd.height W := rfl
  unfold nodeStep
  simp only [hd.announced_eq, hd.sizes_eq, hd.root_eq, hd.shape_eq, hW, hws, not_true_eq_false,
    ↓reduceIte, treeRootM_id, hroot]
  show ∃ kids : List Node, Id.run _ = some kids ∧ ∀ κ ∈ kids, Good κ.2
  have hr' : digestScalars (Id.run (treeRoot blake2sBytes hd.height W)) = hd.root := hr
  simp only [Id.run_bind]
  simp only [hr', ne_eq, not_true_eq_false, ↓reduceIte, hfin, ↓reduceDIte]
  refine forIn_bind_yield_id _ _ (fun k ↦ ∀ κ ∈ k, Good κ.2) ?_ (by simp) _ ?_
  · intro q hqL k hk
    have hq' : q ∈ blindCandidates prog hd.sizes hd.rate pi W := by
      rwa [Finset.mem_toList, Set.Finite.mem_toFinset] at hqL
    obtain ⟨t, hrun, htab, hkids⟩ := hq q hq'
    simp only [hrun]
    rw [show tableOKWith (fun x ↦ (pure (blake2sBytes x) : Id Digest)) (t.blakeRows blakeFree) =
      (pure true : Id Bool) from htab]
    simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [forIn_kids blake2sBytes seed]
    refine ⟨_, rfl, fun κ hκ ↦ ?_⟩
    rcases List.mem_append.mp hκ with hκ | hκ
    · exact hk κ hκ
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hκ
      exact hkids c hc
  · intro k hk
    exact ⟨k, rfl, hk⟩

/-! ## T7′: V_I accepts what the deployed verifier accepts -/

/-- The hash V_I runs with: BLAKE2s, in `Id`. -/
abbrev blakeId : Bytes → Id Digest := fun x ↦ pure (blake2sBytes x)

/-- **The root node** of V_I with BLAKE2s: the root statement's digest under the guest's deployed
seed, and the root's proof. -/
def rootNode (prog : Program) (s : Node.NodeStatement) (ip : IdealProof) : Node :=
  (Node.statementDigest (Node.deployedSeed prog) s, ip.proof)

/-- **The nodes V_I reaches with BLAKE2s** from `root`: the root, and every node of the children a
reached node's step returns. -/
inductive Reached (prog : Program) (ip : IdealProof) (root : Node) : Node → Prop
  /-- The root. -/
  | root : Reached prog ip root root
  /-- A child of a reached node. -/
  | child {ν : Node} {kids : List Node} {κ : Node} : Reached prog ip root ν →
      nodeStep (m := Id) blakeId prog (Node.deployedSeed prog) ip ν = some kids → κ ∈ kids →
      Reached prog ip root κ

/-- **The words cover the reached nodes**: the idealized proof gives every reached node a word of
its stack commitment's width whose BLAKE2s Merkle tree, at the commitment's height, has the node's
stack root. -/
def WordsCover (prog : Program) (ip : IdealProof) (root : Node) : Prop :=
  ∀ ν, Reached prog ip root ν → ∀ hd : Head prog ν.2, ∃ W, ip.word ν = some W ∧
    WellShaped hd.width W ∧ digestScalars (treeRoot blake2sBytes hd.height W) = hd.root

/-- **The reached candidates satisfy Flock's R1CS**: every candidate V_I follows at a reached
node (`blindCandidates`, the relation without Flock) satisfies the leanISA instance's `aux`, so
the full relation `M3Holds`. -/
def CandidatesAux (prog : Program) (ip : IdealProof) (root : Node) : Prop :=
  ∀ ν, Reached prog ip root ν → ∀ hd : Head prog ν.2, ∀ W, ip.word ν = some W →
    ∀ q ∈ blindCandidates prog hd.sizes hd.rate ν.1 W, (leanIsaInstance F₀ prog hd.sizes).aux q

/-- **The reached tables pass the precheck**: no two active non-final `BLAKE2S` rows of a reached
candidate's run with distinct inputs have equal outputs (a BLAKE2s compression collision). -/
def TablesPrecheck (prog : Program) (ip : IdealProof) (root : Node) : Prop :=
  ∀ ν, Reached prog ip root ν → ∀ hd : Head prog ν.2, ∀ W, ip.word ν = some W →
    ∀ q ∈ blindCandidates prog hd.sizes hd.rate ν.1 W, ∀ t, candidateRun prog hd.sizes q = some t →
      Precheck (t.blakeRows blakeFree)

/-- **The fuel suffices**: a size of nodes, at most `fuel` at the root, exceeds the total size of
the children of every reached node (V_I's cost, the closure's steps, within its budget). -/
def FuelBounds (prog : Program) (ip : IdealProof) (root : Node) (fuel : ℕ) : Prop :=
  ∃ sz : Node → ℕ, sz root ≤ fuel ∧ ∀ ν, Reached prog ip root ν → ∀ kids,
    nodeStep (m := Id) blakeId prog (Node.deployedSeed prog) ip ν = some kids →
      (kids.map sz).sum + 1 ≤ sz ν

/-- **A reached node with a head steps**, with children with heads: the word the idealized proof
gives it (`WordsCover`); every candidate satisfies the full relation (`CandidatesAux`), so
runs a deployed execution (`candidateRun_of_m3Holds`) whose rows pass the table check
(`TablesPrecheck`, `tableOKWith_run`) and whose decoded children have heads (`head_of_child`). -/
theorem step_of_reached {ip : IdealProof} {root : Node}
    (hcov : WordsCover Guest.guest ip root) (haux : CandidatesAux Guest.guest ip root)
    (hpre : TablesPrecheck Guest.guest ip root) {ν : Node} (hR : Reached Guest.guest ip root ν)
    (hd : Head Guest.guest ν.2) :
    ∃ kids, nodeStep (m := Id) blakeId Guest.guest (Node.deployedSeed Guest.guest) ip ν =
      some kids ∧ ∀ κ ∈ kids, Nonempty (Head Guest.guest κ.2) := by
  obtain ⟨W, hW, hws, hr⟩ := hcov ν hR hd
  obtain ⟨pi, π⟩ := ν
  refine nodeStep_eq_some hd hW hws hr (fun π ↦ Nonempty (Head Guest.guest π)) fun q hq ↦ ?_
  obtain ⟨hcand, hb⟩ := hq
  have hfull : M3Holds (leanIsaInstance F₀ Guest.guest hd.sizes) (inputOf pi) q :=
    ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, haux _ hR hd W hW q ⟨hcand, hb⟩⟩
  obtain ⟨t, hrun, hv⟩ := candidateRun_of_m3Holds (admissible_of_sizesOf hd.sizes_eq) hfull
  exact ⟨t, hrun, tableOKWith_run hv (hpre _ hR hd W hW q ⟨hcand, hb⟩ t hrun),
    fun c hc ↦ head_of_child hv _ hc⟩

/-- **V_I with BLAKE2s accepts** what the deployed outer verifier accepts, when every reached node
with a head steps to children with heads, within the fuel: V° accepts the root's proof
(`verifyBlind_of_verify`), the outer checks pass (`outerChecksWith_true`), the root's proof has a
head (`head_of_runProof`), and the closure accepts (`closure_accepts`). -/
theorem idealVerify_of_steps {prog : Program} {s : Node.NodeStatement} {ip : IdealProof}
    {fuel : ℕ} (hagg : Node.verifyAggregate prog s ip.proof)
    (hsteps : ∀ ν, Reached prog ip (rootNode prog s ip) ν → Nonempty (Head prog ν.2) →
      ∃ kids, nodeStep (m := Id) blakeId prog (Node.deployedSeed prog) ip ν = some kids ∧
        ∀ κ ∈ kids, Nonempty (Head prog κ.2))
    (hfuel : FuelBounds prog ip (rootNode prog s ip) fuel) :
    idealVerify (m := Id) blakeId prog ip fuel s = true := by
  obtain ⟨⟨hda, hdef⟩, hver⟩ := hagg
  obtain ⟨sz, hroot, hsz⟩ := hfuel
  let Good : Node → Prop := fun ν ↦
    Reached prog ip (rootNode prog s ip) ν ∧ Nonempty (Head prog ν.2)
  let kidsOf : Node → List Node := fun ν ↦
    (nodeStep (m := Id) blakeId prog (Node.deployedSeed prog) ip ν).getD []
  have hstep : ∀ ν, Good ν → nodeStep (m := Id) blakeId prog
      (Node.deployedSeed prog) ip ν = some (kidsOf ν) := by
    rintro ν ⟨hR, hd⟩
    obtain ⟨kids, hk, -⟩ := hsteps ν hR hd
    simp only [kidsOf, hk, Option.getD_some]
  have hhead : Nonempty (Head prog ip.proof) :=
    head_of_runProof (ev := .computed) ((runProof_some blake2sBytes _ _ _).trans (congrArg some hver))
  have hcl := closure_accepts blake2sBytes prog (Node.deployedSeed prog) ip Good kidsOf sz hstep
    (by
      rintro ν ⟨hR, hd⟩ κ hκ
      obtain ⟨kids, hk, hh⟩ := hsteps ν hR hd
      have hκ' : κ ∈ kids := by simpa [kidsOf, hk] using hκ
      exact ⟨Reached.child hR hk hκ', hh κ hκ'⟩)
    (fun ν hν ↦ hsz ν hν.1 _ (hstep ν hν)) fuel [rootNode prog s ip] []
    (fun ν hν ↦ by rw [List.mem_singleton.mp hν]; exact ⟨Reached.root, hhead⟩)
    (by simpa using hroot)
  exact idealVerify_accepts blake2sBytes prog ip fuel s (verifyBlind_of_verify hver)
    (outerChecksWith_true blake2sBytes prog s
      (fun c hc ↦ (hda c hc).trans (Da.vectorDigestOfWith_id c.1).symm)
      (Node.DeferredClaim.bytecodeHolds_of_holds hdef)) hcl

/-- **T7′ (sanity): V_I with BLAKE2s accepts what the deployed aggregation accepts.** The outer
verifier accepts the root statement `s` and the idealized proof's root proof
(`Node.verifyAggregate`); the idealized proof's words cover the stack commitments of the nodes
V_I reaches (`WordsCover`); every candidate V_I follows there satisfies Flock's R1CS
(`CandidatesAux`) and its table passes the precheck (`TablesPrecheck`); the fuel suffices
(`FuelBounds`). Then V_I, run in `Id` with BLAKE2s, accepts, whatever frames the idealized proof
names. -/
theorem idealVerify_blake2s {s : Node.NodeStatement} {ip : IdealProof} {fuel : ℕ}
    (hagg : Node.verifyAggregate Guest.guest s ip.proof)
    (hcov : WordsCover Guest.guest ip (rootNode Guest.guest s ip))
    (haux : CandidatesAux Guest.guest ip (rootNode Guest.guest s ip))
    (hpre : TablesPrecheck Guest.guest ip (rootNode Guest.guest s ip))
    (hfuel : FuelBounds Guest.guest ip (rootNode Guest.guest s ip) fuel) :
    idealVerify (m := Id) blakeId Guest.guest ip fuel s = true :=
  idealVerify_of_steps hagg (fun _ hR ⟨hd⟩ ↦ step_of_reached hcov haux hpre hR hd) hfuel

end
end LeanVM.E2E.Sanity
