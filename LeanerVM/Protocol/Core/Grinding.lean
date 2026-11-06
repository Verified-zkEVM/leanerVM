/-
  LeanerVM.Protocol.Core.Grinding

  The grinding checks of the verifier's history pass in the log the verifier was replayed on.
-/

module

public import LeanerVM.Protocol.LeanVmReader

/-!
# The grinding checks a replayed walk passes

The verifier's chain walk replayed on a log, every hash answered from it and recorded, checks
each grinding nonce: it asks the grinding base of the state, then the check of the nonce against
the base, and absorbs the nonce. Every query the replay records keeps an invariant
(`NonceChecked`): if it absorbs a nonce from a state, the nonce passes its grinding check from
that state in the log, or the state is the answer to a grinding base. The invariant is carried
along the walk by a grade on the replayed reader (`walkChain_grade`) that counts a check at the
deployed bits as nothing and every other check as one: the walk checks only at the deployed bits,
so its count is zero (`nonceChecked_of_walkChain`).

On a log with no collision, no state of a history past its start is the answer to a grinding
base, since it is the answer to the history's previous step; so every nonce of a history whose
steps keep the invariant and that opens with an observe passes its grinding check in the log
(`powPasses_of_history`). The start itself may answer a grinding base: a first state's input with
the lanes `0, 0, 0, 3` is the grinding base's input from the seed.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Verify ChainLog DecodeChain
open OracleSpec

@[expose] public section

namespace Core

/-- A query that absorbs a nonce passes its grinding check, or starts from a grinding base. -/
def NonceChecked (l : hashSpec.QueryLog) (e : (_ : List UInt8) × Digest) : Prop :=
  ∀ cv n, e.1 = absorbInput cv n →
    PowPasses LeanerVM.Parameters.Whir.queryGrindingBits l cv n ∨
      ∃ cv', MerkleTree.logAnswer l (baseInput cv') = some cv

/-- Runs of the replayed reader whose recorded queries keep `NonceChecked`, when their count is
zero. -/
private def powGrade (l : hashSpec.QueryLog) : MonadGrade RW where
  P a k := ∀ st log x st' log', runReplay a st log = some (.ok (x, st'), log') →
    ∃ L, log' = log ++ L ∧ (k = 0 → ∀ e ∈ L, NonceChecked l e)
  pure x st log y st' log' h := by
    rw [runReplay_pure] at h
    simp only [Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp, fun _ e he ↦ nomatch he⟩
  bind {α β a f n k} ha hf st log y st'' log'' h := by
    rw [runReplay_bind] at h
    rcases hr : runReplay a st log with _ | ⟨_ | ⟨x, st'⟩, log'⟩ <;> rw [hr] at h
    · cases h
    · cases h
    obtain ⟨L₁, rfl, h₁⟩ := ha st log x st' log' hr
    obtain ⟨L₂, rfl, h₂⟩ := hf x st' _ y st'' log'' h
    refine ⟨L₁ ++ L₂, by simp, fun hk e he ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact h₁ (by omega) e he
    · exact h₂ (by omega) e he

/-- The counts of the grinding invariant: a check at the deployed bits counts nothing, every other
check counts one, and nothing else counts. -/
private def powCounts : StepCounts :=
  ⟨0, 0, 0, fun bits ↦ if bits = LeanerVM.Parameters.Whir.queryGrindingBits then 0 else 1⟩

private theorem not_absorb_observe {cv cv' : Digest} {y n : E} :
    Block.input cv (.observe y) ≠ absorbInput cv' n := by
  intro h
  have := (input_inj h).2
  cases this

private theorem not_absorb_squeeze {cv cv' : Digest} {n : E} :
    Block.input cv .squeeze ≠ absorbInput cv' n := by
  intro h
  have := (input_inj h).2
  cases this

private theorem not_absorb_base {cv cv' : Digest} {n : E} :
    baseInput cv ≠ absorbInput cv' n := by
  intro h
  have h₁ := parse?_baseInput cv
  rw [h, absorbInput, Block.parse?_input] at h₁
  cases h₁

private theorem powGrade_nextScalar (l : hashSpec.QueryLog) :
    (powGrade l).P (Reader.nextScalar (QueryLog.replayImpl (MerkleTree.logAnswer l))) 0 := by
  intro st log x st' log' h
  rcases st with ⟨fs, _ | ⟨y, rest⟩, ms⟩
  · exact nomatch h
  rw [replay_nextScalar] at h
  rcases ha : MerkleTree.logAnswer l (Block.input fs.cv (.observe y)) with _ | u <;> rw [ha] at h
  · exact nomatch h
  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨_, rfl, fun _ e he ↦ ?_⟩
  rw [List.mem_singleton] at he
  subst he
  exact fun cv n h ↦ absurd h not_absorb_observe

private theorem powGrade_sample (l : hashSpec.QueryLog) :
    (powGrade l).P (Reader.sample (QueryLog.replayImpl (MerkleTree.logAnswer l))) 0 := by
  intro st log x st' log' h
  rw [replay_sample] at h
  rcases ha : MerkleTree.logAnswer l (Block.input st.fs.cv .squeeze) with _ | u <;> rw [ha] at h
  · exact nomatch h
  simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨_, rfl, fun _ e he ↦ ?_⟩
  rw [List.mem_singleton] at he
  subst he
  exact fun cv n h ↦ absurd h not_absorb_squeeze

private theorem powGrade_checkPow (l : hashSpec.QueryLog) (bits : ℕ) :
    (powGrade l).P (Reader.checkPow (QueryLog.replayImpl (MerkleTree.logAnswer l)) bits)
      (powCounts.pow bits) := by
  intro st log x st' log' h
  rcases st with ⟨fs, _ | ⟨n, rest⟩, ms⟩
  · exact nomatch h
  simp only [Reader.checkPow, Reader.takeRaw, FsState.checkPow, FsState.powBase, FsState.powOk,
    FsState.absorbNonce, runReplay_bind, runReplay_get, runReplay_modify, runReplay_pure,
    runReplay_liftM, StateT.run_bind, run_replayImpl] at h
  rcases ha₁ : MerkleTree.logAnswer l (FsState.stepBytes fs.cv 0 FsState.powBaseTag) with _ | b₁ <;>
    simp only [ha₁, Option.bind_none, Option.bind_some] at h
  · exact nomatch h
  rcases ha₃ : MerkleTree.logAnswer l (FsState.stepBytes fs.cv n FsState.powNonceTag) with _ | u
  · by_cases hb : bits = 0 <;> simp [hb, StateT.run_bind, StateT.run_map, run_replayImpl, ha₃] at h
  by_cases hb : bits = 0
  · simp [hb, StateT.run_map, run_replayImpl, ha₃] at h
    split at h
    · rw [runReplay_pure, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, rfl, fun hk ↦ ?_⟩
      exfalso
      simp only [powCounts, hb] at hk
      exact absurd hk (by decide)
    · exact nomatch h
  · rcases ha₂ : MerkleTree.logAnswer l (FsState.stepBytes b₁ n FsState.powNonceTag) with _ | b₂
    · simp [hb, StateT.run_bind, StateT.run_map, run_replayImpl, ha₂, ha₃] at h
    simp [hb, StateT.run_bind, StateT.run_map, run_replayImpl, ha₂, ha₃] at h
    split at h
    · rename_i hok
      rw [runReplay_pure, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨[⟨FsState.stepBytes fs.cv 0 FsState.powBaseTag, b₁⟩,
        ⟨FsState.stepBytes b₁ n FsState.powNonceTag, b₂⟩,
        ⟨FsState.stepBytes fs.cv n FsState.powNonceTag, u⟩], by simp, fun hk e he ↦ ?_⟩
      have hq : bits = LeanerVM.Parameters.Whir.queryGrindingBits := by
        by_contra hne
        simp [powCounts, hne] at hk
      subst hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact fun cv n h ↦ absurd h not_absorb_base
      · intro cv m hcv
        have hcv' : Block.input b₁ (.nonce n) = Block.input cv (.nonce m) := hcv
        exact .inr ⟨fs.cv, by
          rw [← (input_inj hcv').1]
          exact ha₁⟩
      · intro cv m hcv
        have hcv' : Block.input fs.cv (.nonce n) = Block.input cv (.nonce m) := hcv
        obtain ⟨rfl, hb'⟩ := input_inj hcv'
        cases hb'
        exact .inl ⟨b₁, b₂, ha₁, ha₂, by simpa using hok⟩
    · exact nomatch h

private theorem powGrade_throw (l : hashSpec.QueryLog) {α : Type} (e : ReadError) :
    (powGrade l).P (throw e : RW α) 0 := by
  intro st log x st' log' h
  rw [runReplay_throw] at h
  cases h

private theorem powGrade_nextRoot (l : hashSpec.QueryLog) :
    (powGrade l).P (Reader.nextRoot (QueryLog.replayImpl (MerkleTree.logAnswer l))) 0 :=
  (powGrade l).of_eq ((powGrade l).bind (powGrade_nextScalar l) fun a ↦
    (powGrade l).bind (powGrade_nextScalar l) fun b ↦ by
      split
      · exact (powGrade l).pure _
      · exact powGrade_throw l _) rfl

/-- The replayed reader's primitives, graded by the grinding invariant. -/
private theorem powGraded (l : hashSpec.QueryLog) :
    ChainOps.Graded (powGrade l) (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer l)))
      powCounts :=
  ⟨powGrade_nextScalar l, powGrade_sample l, powGrade_nextRoot l, powGrade_checkPow l⟩

private theorem powCounts_positions (depth : ℕ) :
    ∀ fuel need, powCounts.positions depth fuel need = 0
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | fuel + 1, need + 1 => by
    simp only [StepCounts.positions, powCounts_positions depth fuel]
    rfl

private theorem powCounts_tail : ∀ k, powCounts.tail k = 0
  | 0 => rfl
  | k + 1 => by
    simp only [StepCounts.tail, powCounts_tail k]
    simp [powCounts]

private theorem powCounts_layers : ∀ (rs : List ℕ) (j : ℕ), powCounts.layers rs j = 0
  | [], _ => rfl
  | ρ :: rest, j => by
    simp only [StepCounts.layers, powCounts_layers rest]
    simp [StepCounts.layer, StepCounts.rounds, StepCounts.round, powCounts]

private theorem powCounts_levels : ∀ shs : List LevelShape, powCounts.levels shs = 0
  | [] => rfl
  | sh :: shs => by
    simp only [StepCounts.levels, StepCounts.level, powCounts_positions, powCounts_tail,
      powCounts_levels shs]
    simp [StepCounts.folds, powCounts]

private theorem powCounts_chain (prog : Program) (s : Sizes) (input : PublicInput)
    (shs : List LevelShape) : powCounts.chain prog s input shs = 0 := by
  have hl := powCounts_layers
  have hv := powCounts_levels
  simp only [StepCounts.chain, StepCounts.setup, StepCounts.bus, StepCounts.tables,
    StepCounts.pub, StepCounts.flock, StepCounts.whir, StepCounts.rounds, StepCounts.round, hl,
    hv]
  simp [powCounts]

/-- **The replayed chain walk keeps the grinding invariant**: every query a replayed chain walk
that succeeds records absorbs no nonce, or passes its grinding check, or starts from a grinding
base. -/
theorem nonceChecked_of_walkChain {l : hashSpec.QueryLog} {prog : Program} {s : Sizes}
    {input : PublicInput} {shs : List LevelShape} {st st' : ReaderState PrunedMerklePaths}
    {log log' : hashSpec.QueryLog} {w : Wire}
    (h : runReplay (walkChain (readerOps (QueryLog.replayImpl (MerkleTree.logAnswer l))) prog s
      input shs) st log = some (.ok (w, st'), log')) :
    ∃ L, log' = log ++ L ∧ ∀ e ∈ L, NonceChecked l e := by
  obtain ⟨L, hL, hinv⟩ := walkChain_grade (powGraded l) prog s input shs st log w st' log' h
  exact ⟨L, hL, hinv (powCounts_chain prog s input shs)⟩

/-- The step of a chain at a position is among the chain's queries. -/
theorem mem_queries_of_getElem {cv : Digest} {hist : List (Block × Digest)} {j : ℕ}
    {b : Block} {d : Digest} (h : hist[j]? = some (b, d)) :
    (⟨Block.input (HashChain.last cv (hist.take j)) b, d⟩ : (_ : List UInt8) × Digest) ∈
      HashChain.queries Block.input cv hist := by
  have hj : j < hist.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have hsplit : hist.take j ++ (b, d) :: hist.drop (j + 1) = hist := by
    rw [List.getElem?_eq_getElem hj, Option.some.injEq] at h
    conv_rhs => rw [← List.take_append_drop j hist]
    rw [List.drop_eq_getElem_cons hj, h]
  have key : ∀ pre post : List (Block × Digest),
      (⟨Block.input (HashChain.last cv pre) b, d⟩ : (_ : List UInt8) × Digest) ∈
        HashChain.queries Block.input cv (pre ++ (b, d) :: post) := by
    intro pre post
    rw [HashChain.queries_append]
    simp [HashChain.queries]
  have := key (hist.take j) (hist.drop (j + 1))
  rwa [hsplit] at this

/-- **The grinding checks of a history pass in the log**: on a log with no collision, holding
every step of a history from a start `σ` that opens with an observe and whose steps keep the
grinding invariant, every nonce of the history passes its grinding check in the log. -/
theorem powPasses_of_history {l : hashSpec.QueryLog} (hcoll : ¬ QueryLog.HasCollision l)
    {σ : Digest} {hist : List Reading} (h₀ : ∃ x d, hist[0]? = some (.observe x, d))
    (hchain : ∀ e ∈ HashChain.queries Block.input σ hist, e ∈ l)
    (hinv : ∀ e ∈ HashChain.queries Block.input σ hist, NonceChecked l e) :
    ∀ (j : ℕ) n d, hist[j]? = some (.nonce n, d) →
      PowPasses LeanerVM.Parameters.Whir.queryGrindingBits l
        (HashChain.last σ (hist.take j)) n := by
  intro j n d hj
  rcases hinv _ (mem_queries_of_getElem hj) _ n rfl with hp | ⟨cv', hb⟩
  · exact hp
  exfalso
  have hbm := MerkleTree.mem_of_logAnswer_eq_some hb
  rcases j with _ | k
  · obtain ⟨x, d', h₀⟩ := h₀
    rw [hj, Option.some.injEq, Prod.mk.injEq] at h₀
    cases h₀.1
  have hk : k < hist.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hk' : hist[k]? = some (hist[k].1, hist[k].2) := by rw [List.getElem?_eq_getElem hk]
  have hlast : HashChain.last σ (hist.take (k + 1)) = hist[k].2 := by
    rw [List.take_succ_eq_append_getElem hk, HashChain.last_append]
    rfl
  have hq := hchain _ (mem_queries_of_getElem hk')
  refine hcoll ⟨_, hbm, _, hq, fun he ↦ ?_, by rw [hlast]⟩
  have he' : baseInput cv' = Block.input (HashChain.last σ (hist.take k)) hist[k].1 := he
  have h₁ := parse?_baseInput cv'
  rw [he', Block.parse?_input] at h₁
  cases h₁

end Core

end

end LeanerVM.Protocol
