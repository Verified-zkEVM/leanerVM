/-
  LeanVM.Arithmetization.CompletenessB.Satisfied

  The witness of a list of skeletons executing under a semantics of canonical `BLAKE2S` rows
  satisfies the constraint statement without the compression (`SatisfiedByB`).
-/

module

public import LeanVM.Arithmetization.CompletenessB.Rows
public import LeanVM.Arithmetization.Completeness.Satisfied
public import LeanVM.Arithmetization.Soundness.Bus

@[expose] public section

/-!
# The witness under a semantics of `BLAKE2S`

`Completeness/Bus.lean` and `Completeness/Satisfied.lean` with the skeletons executing under a
semantics `Sm` whose `BLAKE2S` rows are canonical (`Fact (Canonical Sm)`): the successor of a
skeleton is its successor under `Sm` (`nextOfB`), and a row sends what `rowOf_sendsB` says
(`PRow.sendsB`). Every declaration here is its deployed namesake without the `B`, the execution
under `Sm`; the declarations that do not mention the semantics are the deployed ones, reused. The
conclusion is `SatisfiedByB` (`Soundness/Bus.lean`), `SatisfiedBy` without the compression of the
`BLAKE2S` rows, which no other conjunct reads.
-/

open scoped List

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {Sm : BlakeSem} [hSm : Fact (Canonical Sm)]

/-- The state a skeleton steps to over the image `img`: the successor `execute` computes, the
state itself if the instruction fails. -/
noncomputable def nextOfB (Sm : BlakeSem) {κ : ℕ} (img : MemImage κ) (sk : Skel) : Regs K :=
  (executeWithB Sm img.read sk.regs sk.ins).getD sk.regs

/-- A skeleton is sound for the program and the image: the program fetches its instruction at its
counter, and the instruction executes from its state. -/
def SkelOkB (Sm : BlakeSem) {κ : ℕ} (prog : Program) (img : MemImage κ) (sk : Skel) : Prop :=
  prog.fetch sk.pc = some sk.ins ∧ ∃ next, executeWithB Sm img.read sk.regs sk.ins = some next

/-- What a row of the witness sends. -/
noncomputable def PRow.sendsB (Sm : BlakeSem) {κ : ℕ} (img : MemImage κ) (r : PRow) : List (String × Array K) :=
  sendsOf r.sk.pc r.sk.fp (nextOfB Sm img r.sk) (g ^ r.bc) (entry r.sk.ins)
    (readsOf img r.sk.fp r.cnt r.sk.ins)

/-- The row circuit of a row of an executing skeleton sends what `PRow.sendsB` says. -/
theorem PRow.rowSends_rawB {κ : ℕ} {img : MemImage κ} {r : PRow}
    (h : ∃ next, executeWithB Sm img.read r.sk.regs r.sk.ins = some next) (data : ProverData K) :
    rowSends (opComponent r.sk.ins.opcode) (Environment.fromArray (r.raw img) data) =
      r.sendsB Sm img := by
  obtain ⟨next, hn⟩ := h
  have := rowOf_sendsB hSm.out hn r.cnt (g ^ r.bc) data
  rw [PRow.raw, this, PRow.sendsB]
  simp [nextOfB, hn]

omit hSm in
/-- A row's memory pulls are the messages of the cells it reads, numbered as its row says. -/
theorem PRow.memPulls_eqB {κ : ℕ} (img : MemImage κ) (r : PRow)
    (h : r.exps.length = (readAddrs img r.sk.fp r.sk.ins).length) :
    ((r.sendsB Sm img).filter (·.1 = MemPull.name)).map (·.2) =
      List.zipWith (fun a e ↦ memMsg img a e) (readAddrs img r.sk.fp r.sk.ins) r.exps := by
  rw [PRow.sendsB, sendsOf_memPull, readsOf]
  have := mapIdx_eq_zipWith (fun a e ↦ ((a, g ^ e, img.limbsAt a) : K × K × Vector K 3)) r.exps
    (readAddrs img r.sk.fp r.sk.ins) h
  simp only [PRow.cnt] at *
  rw [this, List.map_zipWith]
  rfl

omit hSm in
/-- A row's memory pushes are the messages of the cells it reads, numbered one higher. -/
theorem PRow.memPushes_eqB {κ : ℕ} (img : MemImage κ) (r : PRow)
    (h : r.exps.length = (readAddrs img r.sk.fp r.sk.ins).length) :
    ((r.sendsB Sm img).filter (·.1 = MemPush.name)).map (·.2) =
      List.zipWith (fun a e ↦ memMsg img a (e + 1)) (readAddrs img r.sk.fp r.sk.ins) r.exps := by
  rw [PRow.sendsB, sendsOf_memPush, readsOf]
  have := mapIdx_eq_zipWith (fun a e ↦ ((a, g ^ e, img.limbsAt a) : K × K × Vector K 3)) r.exps
    (readAddrs img r.sk.fp r.sk.ins) h
  simp only [PRow.cnt] at *
  rw [this, List.map_zipWith]
  congr 1
  funext a e
  simp only [memMsg, pow_succ']

omit hSm in
/-- The memory pulls of the rows of a list of skeletons are the messages of its reads, numbered by
the chain: the reads of the list, in order, with the numbers from the counters `sm`. -/
theorem mkRows_memPullsB {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap (fun r ↦ ((r.sendsB Sm img).filter (·.1 = MemPull.name)).map (·.2)) =
      List.zipWith (fun a e ↦ memMsg img a e) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps sm (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons]
    rw [ih, readExps_append, List.zipWith_append (by rw [readExps_length])]
    congr 1
    exact PRow.memPulls_eqB img ⟨sk, readExps sm (readAddrs img sk.fp sk.ins), sb sk.pc⟩
      (readExps_length _ _)

omit hSm in
/-- The memory pushes of the rows of a list of skeletons, likewise. -/
theorem mkRows_memPushesB {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap (fun r ↦ ((r.sendsB Sm img).filter (·.1 = MemPush.name)).map (·.2)) =
      List.zipWith (fun a e ↦ memMsg img a (e + 1))
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps sm (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons]
    rw [ih, readExps_append, List.zipWith_append (by rw [readExps_length])]
    congr 1
    exact PRow.memPushes_eqB img ⟨sk, readExps sm (readAddrs img sk.fp sk.ins), sb sk.pc⟩
      (readExps_length _ _)

omit hSm in
/-- A row of a skeleton the program fetches pulls the bytecode entry at its counter with its
number. -/
theorem PRow.bcPulls_eqB {κ : ℕ} {prog : Program} (img : MemImage κ) (r : PRow)
    (h : prog.fetch r.sk.pc = some r.sk.ins) :
    ((r.sendsB Sm img).filter (·.1 = BytecodePull.name)).map (·.2) = [bcMsg prog r.sk.pc r.bc] := by
  rw [PRow.sendsB, sendsOf_bcPull, bcMsg, entryAt, h]

omit hSm in
/-- … and pushes it with the next. -/
theorem PRow.bcPushes_eqB {κ : ℕ} {prog : Program} (img : MemImage κ) (r : PRow)
    (h : prog.fetch r.sk.pc = some r.sk.ins) :
    ((r.sendsB Sm img).filter (·.1 = BytecodePush.name)).map (·.2) =
      [bcMsg prog r.sk.pc (r.bc + 1)] := by
  rw [PRow.sendsB, sendsOf_bcPush, bcMsg, entryAt, h, pow_succ']

omit hSm in
/-- The bytecode pulls of the rows of a list of fetched skeletons are the messages of their
counters, numbered by the chain over the counters. -/
theorem mkRows_bcPullsB {κ : ℕ} {prog : Program} (img : MemImage κ) (sm sb : K → ℕ)
    (S : List Skel) (hS : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sendsB Sm img).filter (·.1 = BytecodePull.name)).map (·.2)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc e) (S.map (·.pc)) (readExps sb (S.map (·.pc))) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons, List.map_cons, readExps, List.zipWith_cons_cons]
    rw [PRow.bcPulls_eqB img _ (hS sk List.mem_cons_self)]
    simp only [List.singleton_append]
    congr 1
    exact ih _ _ fun sk' h ↦ hS sk' (List.mem_cons_of_mem _ h)

omit hSm in
/-- The bytecode pushes of the rows of a list of fetched skeletons, likewise. -/
theorem mkRows_bcPushesB {κ : ℕ} {prog : Program} (img : MemImage κ) (sm sb : K → ℕ)
    (S : List Skel) (hS : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sendsB Sm img).filter (·.1 = BytecodePush.name)).map (·.2)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc (e + 1)) (S.map (·.pc))
        (readExps sb (S.map (·.pc))) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons, List.map_cons, readExps, List.zipWith_cons_cons]
    rw [PRow.bcPushes_eqB img _ (hS sk List.mem_cons_self)]
    simp only [List.singleton_append]
    congr 1
    exact ih _ _ fun sk' h ↦ hS sk' (List.mem_cons_of_mem _ h)

omit hSm in
/-- The state pulls of the rows are the states of the skeletons. -/
theorem mkRows_statePullsB {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sendsB Sm img).filter (·.1 = StatePull.name)).map (·.2)) =
      S.map fun sk ↦ #[sk.pc, sk.fp] := by
  have h : ∀ r : PRow, ((r.sendsB Sm img).filter (·.1 = StatePull.name)).map (·.2) =
      [#[r.sk.pc, r.sk.fp]] := fun r ↦ sendsOf_statePull _ _ _ _ _ _
  simp only [h]
  rw [flatMap_singleton_eq_map]
  calc (mkRows img sm sb S).map (fun r ↦ #[r.sk.pc, r.sk.fp])
      = ((mkRows img sm sb S).map (·.sk)).map (fun sk ↦ #[sk.pc, sk.fp]) := by
        rw [List.map_map]; rfl
    _ = S.map (fun sk ↦ #[sk.pc, sk.fp]) := by rw [mkRows_sk]

omit hSm in
/-- The state pushes of the rows are the successors of the skeletons. -/
theorem mkRows_statePushesB {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sendsB Sm img).filter (·.1 = StatePush.name)).map (·.2)) =
      S.map fun sk ↦ #[(nextOfB Sm img sk).pc, (nextOfB Sm img sk).fp] := by
  have h : ∀ r : PRow, ((r.sendsB Sm img).filter (·.1 = StatePush.name)).map (·.2) =
      [#[(nextOfB Sm img r.sk).pc, (nextOfB Sm img r.sk).fp]] := fun r ↦ sendsOf_statePush _ _ _ _ _ _
  simp only [h]
  rw [flatMap_singleton_eq_map]
  calc (mkRows img sm sb S).map (fun r ↦ #[(nextOfB Sm img r.sk).pc, (nextOfB Sm img r.sk).fp])
      = ((mkRows img sm sb S).map (·.sk)).map
          (fun sk ↦ #[(nextOfB Sm img sk).pc, (nextOfB Sm img sk).fp]) := by
        rw [List.map_map]; rfl
    _ = S.map (fun sk ↦ #[(nextOfB Sm img sk).pc, (nextOfB Sm img sk).fp]) := by rw [mkRows_sk]

/-- The sends of an opcode's table are those of its rows, when their instructions execute. -/
theorem opTable_sendsB {κ : ℕ} (img : MemImage κ) (data : ProverData K) (R : List PRow)
    (op : Opcode) (hR : ∀ r ∈ R, ∃ next, executeWithB Sm img.read r.sk.regs r.sk.ins = some next) :
    (opTable img data R op).table.flatMap
        (fun row ↦ rowSends (opTable img data R op).component
          ((opTable img data R op).environment row)) =
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sendsB Sm img) := by
  show ((R.filter fun r ↦ r.sk.ins.opcode = op).map (PRow.raw img)).flatMap
    (fun row ↦ rowSends (opComponent op) (Environment.fromArray row data)) = _
  rw [List.flatMap_map]
  refine List.flatMap_congr fun r hr ↦ ?_
  obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
  simp only [decide_eq_true_eq] at hr2
  subst hr2
  exact PRow.rowSends_rawB (hR r hr1) data

/-- Everything the witness sends, in the ensemble's order: the verifier's two messages, the
rows of the six tables, the memory block, the bytecode block. -/
noncomputable def skelSendsB (Sm : BlakeSem) (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel) :
    List (String × Array K) :=
  [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] ++
    (tableOpcodes.flatMap fun op ↦
      ((skelRows img S).filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sendsB Sm img)) ++
    memBlockSends img (skelMemFin img S) ++ bcBlockSends prog (skelBcFin S)

/-- **The sends of the witness.** -/
theorem skelWitness_sendsB (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, executeWithB Sm img.read sk.regs sk.ins = some next) :
    ((skelWitness prog input img S).allTables.flatMap fun t ↦ t.table.flatMap fun row ↦
      rowSends t.component (t.environment row)) = skelSendsB Sm prog img S := by
  have hR : ∀ r ∈ skelRows img S, ∃ next, executeWithB Sm img.read r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  have hV : ∀ (w : EnsembleWitness (leanIsaEnsemble prog)),
      (w.verifierTable.table.flatMap fun row ↦
        rowSends w.verifierTable.component (w.verifierTable.environment row)) =
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] := fun w ↦ by
    simp only [EnsembleWitness.verifierTable, List.flatMap_singleton]
    exact verifier_sends prog _
  simp only [EnsembleWitness.allTables, skelWitness, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hV]
  simp only [opTable_sendsB _ _ _ _ hR, memBlock_sends, bcBlock_sends, skelSendsB, tableOpcodes,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

omit hSm in
/-- **The six tables hold the rows of `R` regrouped by opcode**: on every channel their messages
are a permutation of those of the rows in order. -/
theorem chanOf_tables_permB {κ : ℕ} (img : MemImage κ) (n : String) (R : List PRow) :
    (chanOf n (tableOpcodes.flatMap fun op ↦
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sendsB Sm img))).Perm
      (R.flatMap fun r ↦ chanOf n (r.sendsB Sm img)) := by
  rw [chanOf_flatMap]
  have h : (tableOpcodes.flatMap fun op ↦ chanOf n
      ((R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sendsB Sm img))) =
      (tableOpcodes.flatMap fun op ↦ R.filter fun r ↦ r.sk.ins.opcode = op).flatMap
        fun r ↦ chanOf n (r.sendsB Sm img) := by
    rw [List.flatMap_assoc]
    refine List.flatMap_congr fun op _ ↦ ?_
    rw [chanOf_flatMap]
  rw [h]
  exact (regroup_perm tableOpcodes (fun r : PRow ↦ r.sk.ins.opcode) R (by decide)
    fun r _ ↦ mem_tableOpcodes _).flatMap_right _

omit hSm in
/-- The witness's messages on a channel: the verifier's, the rows' of the six tables in
order, the memory block's, the bytecode block's, up to the regrouping of the rows. -/
theorem chanOf_skelSends_permB (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (n : String) :
    (chanOf n (skelSendsB Sm prog img S)).Perm
      (chanOf n [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] ++
        (skelRows img S).flatMap (fun r ↦ chanOf n (r.sendsB Sm img)) ++
        chanOf n (memBlockSends img (skelMemFin img S)) ++
        chanOf n (bcBlockSends prog (skelBcFin S))) := by
  unfold skelSendsB
  simp only [chanOf_append]
  exact (((chanOf_tables_permB img n (skelRows img S)).append_left _).append_right _).append_right _

/-- **The memory pair balances**: the rows' reads, numbered by the chain, against the block's seeds
and finalizes. -/
theorem mem_pair_permB (prog : Program) {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, executeWithB Sm img.read sk.regs sk.ins = some next) :
    (chanOf MemPush.name (skelSendsB Sm prog img S)).Perm
      (chanOf MemPull.name (skelSendsB Sm prog img S)) := by
  have hκ64 : κ < 64 := by unfold maxLogMem at hκ; omega
  have hmem : ∀ a ∈ S.flatMap (fun sk ↦ readAddrs img sk.fp sk.ins),
      a ∈ (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ gpow (i : ℕ) := by
    intro a ha
    obtain ⟨sk, hsk, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨next, hn⟩ := hS sk hsk
    obtain ⟨w, hw⟩ := readAddrs_validB hSm.out (pc := sk.pc) (fp := sk.fp) hn a ha
    obtain ⟨i, rfl, -⟩ := (MemImage.read_eq_some_iff hκ64 img).mp hw
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hb := block_balance _ (gpow_keys_nodup κ hκ) (memMsg img) _ hmem
  have h1 : (skelRows img S).flatMap (fun r ↦ chanOf MemPush.name (r.sendsB Sm img)) =
      List.zipWith (fun a e ↦ memMsg img a (e + 1))
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) :=
    mkRows_memPushesB img (fun _ ↦ 0) (fun _ ↦ 0) S
  have h2 : (skelRows img S).flatMap (fun r ↦ chanOf MemPull.name (r.sendsB Sm img)) =
      List.zipWith (fun a e ↦ memMsg img a e)
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) :=
    mkRows_memPullsB img (fun _ ↦ 0) (fun _ ↦ 0) S
  have hv1 : chanOf MemPush.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, MemPush])
  have hv2 : chanOf MemPull.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, MemPull])
  have hc1 : chanOf MemPush.name (bcBlockSends prog (skelBcFin S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases bcBlockSends_names prog _ x hx with h | h <;> simp [h, MemPush, BytecodePush,
        BytecodePull]
  have hc2 : chanOf MemPull.name (bcBlockSends prog (skelBcFin S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases bcBlockSends_names prog _ x hx with h | h <;> simp [h, MemPull, BytecodePush,
        BytecodePull]
  refine (chanOf_skelSends_permB prog img S _).trans
    (List.Perm.trans ?_ (chanOf_skelSends_permB prog img S _).symm)
  rw [hv1, hv2, hc1, hc2, h1, h2, memBlock_push hκ64, memBlock_pull hκ64]
  simp only [List.nil_append, List.append_nil]
  simpa only [List.map_map, Function.comp_def, skelMemFin] using hb

omit hSm in
/-- **The bytecode pair balances**: the rows' fetches, numbered by the chain, against the block's
seeds and finalizes. -/
theorem bc_pair_permB (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (hS : ∀ sk ∈ S, SkelOkB Sm prog img sk) :
    (chanOf BytecodePush.name (skelSendsB Sm prog img S)).Perm
      (chanOf BytecodePull.name (skelSendsB Sm prog img S)) := by
  have hmem : ∀ a ∈ S.map (·.pc),
      a ∈ (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        gpow (i : ℕ) := by
    intro a ha
    obtain ⟨sk, hsk, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi, -⟩ := Program.fetch_eq_some_iff prog |>.mp (hS sk hsk).1
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, hi.symm⟩
  have hb := block_balance _ (gpow_keys_nodup prog.logSize prog.logSize_le) (bcMsg prog) _ hmem
  have hF : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins := fun sk h ↦ (hS sk h).1
  have h1 : (skelRows img S).flatMap (fun r ↦ chanOf BytecodePush.name (r.sendsB Sm img)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc (e + 1)) (S.map (·.pc))
        (readExps (fun _ ↦ 0) (S.map (·.pc))) :=
    mkRows_bcPushesB img (fun _ ↦ 0) (fun _ ↦ 0) S hF
  have h2 : (skelRows img S).flatMap (fun r ↦ chanOf BytecodePull.name (r.sendsB Sm img)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc e) (S.map (·.pc))
        (readExps (fun _ ↦ 0) (S.map (·.pc))) :=
    mkRows_bcPullsB img (fun _ ↦ 0) (fun _ ↦ 0) S hF
  have hv1 : chanOf BytecodePush.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, BytecodePush])
  have hv2 : chanOf BytecodePull.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] = [] :=
    chanOf_eq_nil (by simp [StatePush, StatePull, BytecodePull])
  have hc1 : chanOf BytecodePush.name (memBlockSends img (skelMemFin img S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases memBlockSends_names img _ x hx with h | h <;> simp [h, MemPush, MemPull,
        BytecodePush]
  have hc2 : chanOf BytecodePull.name (memBlockSends img (skelMemFin img S)) = [] :=
    chanOf_eq_nil fun x hx ↦ by
      rcases memBlockSends_names img _ x hx with h | h <;> simp [h, MemPush, MemPull,
        BytecodePull]
  refine (chanOf_skelSends_permB prog img S _).trans
    (List.Perm.trans ?_ (chanOf_skelSends_permB prog img S _).symm)
  rw [hv1, hv2, hc1, hc2, h1, h2, bcBlock_push, bcBlock_pull]
  simp only [List.nil_append, List.append_nil]
  simpa only [List.map_map, Function.comp_def, skelBcFin] using hb

omit hSm in
/-- **The state pair balances**, from the hypothesis that the skeletons' states and successors
balance with the initial and final states: the rows' pulls and pushes are those states, regrouped
by the six tables. -/
theorem state_pair_permB (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOfB Sm img sk).pc, (nextOfB Sm img sk).fp]).Perm
      (#[prog.finalPc, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp])) :
    (chanOf StatePush.name (skelSendsB Sm prog img S)).Perm
      (chanOf StatePull.name (skelSendsB Sm prog img S)) := by
  have h1 : (skelRows img S).flatMap (fun r ↦ chanOf StatePush.name (r.sendsB Sm img)) =
      S.map fun sk ↦ #[(nextOfB Sm img sk).pc, (nextOfB Sm img sk).fp] :=
    mkRows_statePushesB img (fun _ ↦ 0) (fun _ ↦ 0) S
  have h2 : (skelRows img S).flatMap (fun r ↦ chanOf StatePull.name (r.sendsB Sm img)) =
      S.map fun sk ↦ #[sk.pc, sk.fp] :=
    mkRows_statePullsB img (fun _ ↦ 0) (fun _ ↦ 0) S
  have hv1 : chanOf StatePush.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] = [#[1, 1]] := by
    simp [chanOf, StatePush, StatePull]
  have hv2 : chanOf StatePull.name
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] =
      [#[prog.finalPc, 1]] := by
    simp [chanOf, StatePush, StatePull]
  have hc : ∀ n, (n = StatePush.name ∨ n = StatePull.name) →
      chanOf n (memBlockSends img (skelMemFin img S)) = [] ∧
        chanOf n (bcBlockSends prog (skelBcFin S)) = [] := by
    intro n hn
    refine ⟨chanOf_eq_nil fun x hx ↦ ?_, chanOf_eq_nil fun x hx ↦ ?_⟩
    · rcases memBlockSends_names img _ x hx with h | h <;>
        rcases hn with rfl | rfl <;> simp [h, StatePush, StatePull, MemPush, MemPull]
    · rcases bcBlockSends_names prog _ x hx with h | h <;>
        rcases hn with rfl | rfl <;> simp [h, StatePush, StatePull, BytecodePush, BytecodePull]
  obtain ⟨hm1, hb1⟩ := hc _ (Or.inl rfl)
  obtain ⟨hm2, hb2⟩ := hc _ (Or.inr rfl)
  refine (chanOf_skelSends_permB prog img S _).trans
    (List.Perm.trans ?_ (chanOf_skelSends_permB prog img S _).symm)
  rw [hv1, hv2, hm1, hb1, hm2, hb2, h1, h2]
  simpa only [List.append_nil, List.singleton_append] using hstate

omit hSm in
/-- A row of the witness has nonzero counts: they are powers of `g`. -/
theorem PRow.sends_counts_ne_zeroB {κ : ℕ} (img : MemImage κ) (r : PRow) :
    ∀ y ∈ r.sendsB Sm img,
      (y.1 = MemPull.name ∨ y.1 = BytecodePull.name) → ∃ h : 1 < y.2.size, y.2[1] ≠ 0 := by
  refine sendsOf_counts_ne_zero (pow_ne_zero _ g_ne_zero) fun x hx ↦ ?_
  simp only [readsOf, List.mem_mapIdx] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact pow_ne_zero _ g_ne_zero

/-- **Every read pull of the six tables carries a nonzero count.** -/
theorem skelWitness_counts_nonzeroB (prog : Program) (input : PublicInput) {κ : ℕ}
    (img : MemImage κ) (S : List Skel)
    (hS : ∀ sk ∈ S, ∃ next, executeWithB Sm img.read sk.regs sk.ins = some next) :
    CountsNonzero (skelWitness prog input img S) := by
  have hR : ∀ r ∈ skelRows img S, ∃ next, executeWithB Sm img.read r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hS _ (mem_mkRows_sk hr)
  have h6 : (skelWitness prog input img S).tables.take 6 =
      tableOpcodes.map (opTable img (imageData img) (skelRows img S)) := rfl
  intro t ht i hi hn h
  rw [h6, List.mem_map] at ht
  obtain ⟨op, -, rfl⟩ := ht
  have hmem := mem_interactions_sends _ hi
  rw [opTable_sendsB img _ _ op hR] at hmem
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hmem
  obtain ⟨h', hne⟩ := PRow.sends_counts_ne_zeroB img _ _ hr hn
  exact hne

/-- The messages the witness sends on a channel. -/
theorem messagesOn_skelWitnessB (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, executeWithB Sm img.read sk.regs sk.ins = some next)
    (c : RawChannel K) :
    messagesOn (skelWitness prog input img S) c = chanOf c.name (skelSendsB Sm prog img S) := by
  rw [messagesOn_eq_sends, skelWitness_sendsB prog input img S hS]
  rfl

/-- **The witness of a list of skeletons satisfies the constraint statement.** When the skeletons
`S` are sound for the program and the image, their state pulls and pushes balance with the
initial and final states, every table has at most `2^maxLogRows` rows, the memory log-size is in
the window and the image has the two
public words, `skelWitness prog input img S` satisfies every conjunct of `SatisfiedByB`. -/
theorem skelWitness_satisfiedByB (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκmin : minLogMem ≤ κ) (hκ : κ ≤ maxLogMem)
    (hS : ∀ sk ∈ S, SkelOkB Sm prog img sk)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOfB Sm img sk).pc, (nextOfB Sm img sk).fp]).Perm
      (#[prog.finalPc, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp]))
    (hrows : ∀ op, Skel.count op S ≤ 2 ^ maxLogRows)
    (hw0 : img.read (gpow 0) = some input.word0) (hw1 : img.read (gpow 1) = some input.word1) :
    SatisfiedByB prog input (skelWitness prog input img S) := by
  have hex : ∀ sk ∈ S, ∃ next, executeWithB Sm img.read sk.regs sk.ins = some next := fun sk h ↦ (hS sk h).2
  obtain ⟨hwa, hwb⟩ := skelWitness_words input img hκ hw0 hw1
  exact
    { public_input_eq := rfl
      constraints := skelWitness_constraints prog input img S
      state_balanced := by
        unfold BalancedPair
        rw [messagesOn_skelWitnessB prog input img S hex, messagesOn_skelWitnessB prog input img S hex]
        exact state_pair_permB prog img S hstate
      mem_balanced := by
        unfold BalancedPair
        rw [messagesOn_skelWitnessB prog input img S hex, messagesOn_skelWitnessB prog input img S hex]
        exact mem_pair_permB prog hκ img S hex
      bytecode_balanced := by
        unfold BalancedPair
        rw [messagesOn_skelWitnessB prog input img S hex, messagesOn_skelWitnessB prog input img S hex]
        exact bc_pair_permB prog img S hS
      counts_nonzero := skelWitness_counts_nonzeroB prog input img S hex
      caps := skelWitness_caps prog input img S hκmin hκ hrows
      index_columns := skelWitness_index_columns prog input img S
      seed_rows := skelWitness_seed_rows prog input img S hκ
      bytecode_rows := skelWitness_bytecode_rows prog input img S
      word0_eq := hwa
      word1_eq := hwb }

end LeanVM.Arithmetization
