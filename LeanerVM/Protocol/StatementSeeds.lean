/-
  LeanerVM.Protocol.StatementSeeds

  The statement a chain state opens, read off a log of the hash: the statement's three seed
  hashes, the program's bytes, the seed's preimage and the first state's input, logged with
  answers that chain into the state.
-/

module

public import LeanerVM.Protocol.ChainGroups

/-!
# The statements a log opens

The verifier computes its chain's first state from the statement through the hash
(`FsState.seedWith`): the program hash `ph` answers the program's bytes (`programBytes`), the seed
`iv` answers the 78 bytes of its preimage (`seedPreimageOf ph`), and the first state `σ` answers
the 64 bytes of the seed and the public input's lanes (`seedInput iv input`). A log logs a seed of
the statement `(prog, input)` at `σ` when it holds the three entries (`SeedLogged`), and
`stmtOf l σ` is a statement whose seed the log logs at `σ`, `none` when there is none. It is
chosen classically and read only in proofs.

* `programBytes_injective`: the program's bytes determine the program, so on a log with no
  collision a state opens one statement at most (`stmtOf_eq_of_seedLogged`).
* `stmtOf_append`: one more query of a clean log, its answer `u` fresh and not in play, opens or
  closes no statement at another state. The answer completes a logged seed only as one of its
  three answers: as the first state it is `u` itself; as the seed it is the first half of a logged
  first-state input (`halves`), as the program hash the slot of a logged preimage
  (`programHashSlot`), and both are in play.
* `stmtOf_dedupKeys`: deduplicating a consistent log changes no statement.
* `stmtOf_eq_none_of_step`, `stmtOf_states_eq_none`: on a log with no collision, a state a logged
  step leads to from a state that answers a 64-byte input opens no statement, since its seed would
  be the state before, which then answers a 78-byte preimage too. So no state of a logged chain
  from a first state is a start.

These are the laws of `ChainStarts` for `stmtOf`, the start test of leanVM's reader.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash OracleSpec

@[expose] public section

/-! ## The program's bytes -/

/-- The program's bytes are eight per word of the bytecode column. -/
theorem length_programBytes (prog : Program) :
    (programBytes prog).length = 2 ^ (prog.logSize + 4) * 8 := by
  simp [programBytes, List.length_flatMap, length_kBytes]

/-- The bytecode column's cell at an instruction and a slot is that slot. -/
private theorem bytecodeColumn_cell (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (bytecodeColumn prog).values[cubeSplit prog.logSize 4 (i, s)] =
      (encodeSlots (prog.code i))[s] := by
  simp [bytecodeColumn]

/-- **The program's bytes determine the program.** -/
theorem programBytes_injective : Function.Injective programBytes := by
  intro p p' h
  have hk : p.logSize = p'.logSize := by
    have hlen := congrArg List.length h
    rw [length_programBytes, length_programBytes] at hlen
    have := Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right (by norm_num) hlen)
    omega
  obtain ⟨k, hk₁, c⟩ := p
  obtain ⟨k', hk₂, c'⟩ := p'
  dsimp only at hk
  subst hk
  have hv : (bytecodeColumn ⟨k, hk₁, c⟩).values = (bytecodeColumn ⟨k, hk₂, c'⟩).values :=
    Vector.toList_inj.mp (flatMap_kBytes_inj h)
  obtain rfl : c = c' := by
    funext i
    refine entry_injective (Vector.ext fun j hj ↦ ?_)
    have h₁ := congrArg (·[cubeSplit k 4 (i, (⟨j + 3, by omega⟩ : Fin 16))]) hv
    have h₃ : 3 ≤ j + 3 ∧ j + 3 < 11 := by omega
    rw [bytecodeColumn_cell, bytecodeColumn_cell] at h₁
    simp only [Fin.getElem_fin, encodeSlots_getElem _ (j + 3) (by omega), h₃] at h₁
    simpa using h₁
  rfl

/-! ## The statement of a state -/

/-- **A log logs a seed** of the statement `st` at the state `σ`: the program's bytes answered by
a program hash `ph`, the seed's preimage of `ph` by a seed `iv`, and the first state's input of
`iv` and the public input by `σ`. -/
def SeedLogged (l : hashSpec.QueryLog) (st : Program × PublicInput) (σ : Digest) : Prop :=
  ∃ ph iv, ⟨programBytes st.1, ph⟩ ∈ l ∧ ⟨seedPreimageOf ph, iv⟩ ∈ l ∧ ⟨seedInput iv st.2, σ⟩ ∈ l

open Classical in
/-- **The statement a state opens**: a statement whose seed the log logs at `σ`, chosen; `none`
when there is none. -/
noncomputable def stmtOf (l : hashSpec.QueryLog) (σ : Digest) : Option (Program × PublicInput) :=
  if h : ∃ st, SeedLogged l st σ then some h.choose else none

/-- A seed logged in part of a log is logged in the log. -/
theorem SeedLogged.mono {l l' : hashSpec.QueryLog} (hsub : ∀ e ∈ l, e ∈ l')
    {st : Program × PublicInput} {σ : Digest} (h : SeedLogged l st σ) : SeedLogged l' st σ :=
  let ⟨ph, iv, h₁, h₂, h₃⟩ := h
  ⟨ph, iv, hsub _ h₁, hsub _ h₂, hsub _ h₃⟩

open Classical in
/-- Logs that log the same seeds at two states give the two states one statement. -/
theorem stmtOf_congr {l l' : hashSpec.QueryLog} {σ σ' : Digest}
    (h : ∀ st, SeedLogged l st σ ↔ SeedLogged l' st σ') : stmtOf l σ = stmtOf l' σ' :=
  congrArg (fun P : Program × PublicInput → Prop ↦ if h : ∃ st, P st then some h.choose else none)
    (funext fun st ↦ propext (h st))

/-- Two inputs of a log with no collision that one digest answers are one input. -/
private theorem input_eq_of_noCollision {l : hashSpec.QueryLog}
    (hcoll : ¬ QueryLog.HasCollision l) {q q' : List UInt8} {d : Digest} (h : ⟨q, d⟩ ∈ l)
    (h' : ⟨q', d⟩ ∈ l) : q = q' :=
  by_contra fun hne ↦ hcoll ⟨_, h, _, h', hne, rfl⟩

/-- On a log with no collision, a state has one logged statement at most. -/
theorem SeedLogged.unique {l : hashSpec.QueryLog} (hcoll : ¬ QueryLog.HasCollision l)
    {st st' : Program × PublicInput} {σ : Digest} (h : SeedLogged l st σ)
    (h' : SeedLogged l st' σ) : st = st' := by
  obtain ⟨ph, iv, h₁, h₂, h₃⟩ := h
  obtain ⟨ph', iv', h₁', h₂', h₃'⟩ := h'
  obtain ⟨rfl, h₄⟩ := seedInput_injective (input_eq_of_noCollision hcoll h₃ h₃')
  obtain rfl := seedPreimageOf_injective (input_eq_of_noCollision hcoll h₂ h₂')
  exact Prod.ext (programBytes_injective (input_eq_of_noCollision hcoll h₁ h₁')) h₄

/-- **A logged seed is the state's statement**, on a log with no collision. -/
theorem stmtOf_eq_of_seedLogged {l : hashSpec.QueryLog} (hcoll : ¬ QueryLog.HasCollision l)
    {st : Program × PublicInput} {σ : Digest} (h : SeedLogged l st σ) : stmtOf l σ = some st := by
  have hex : ∃ st, SeedLogged l st σ := ⟨st, h⟩
  rw [stmtOf, dite_eq_left hex, SeedLogged.unique hcoll hex.choose_spec h]

/-- A state the log logs no seed at opens no statement. -/
theorem stmtOf_eq_none {l : hashSpec.QueryLog} {σ : Digest}
    (h : ∀ st, ¬ SeedLogged l st σ) : stmtOf l σ = none := by
  rw [stmtOf, dite_eq_right fun ⟨st, hst⟩ ↦ h st hst]

/-! ## The laws of the starts -/

/-- **One more clean query** opens or closes no statement but at its answer: an answer not in
play completes no logged seed at another state. -/
theorem stmtOf_append (l : hashSpec.QueryLog) (t : List UInt8) (u d : Digest)
    (hl : CleanLog [] (l ++ [⟨t, u⟩])) (hd : d ≠ u) :
    stmtOf (l ++ [⟨t, u⟩]) d = stmtOf l d := by
  refine stmtOf_congr fun st ↦
    ⟨fun ⟨ph, iv, h₁, h₂, h₃⟩ ↦ ?_, SeedLogged.mono fun e he ↦ List.mem_append_left _ he⟩
  have hu := hl.notInPlay_of_append
  have old : ∀ {q : List UInt8} {a : Digest}, ⟨q, a⟩ ∈ l ++ [⟨t, u⟩] → a ≠ u → ⟨q, a⟩ ∈ l := by
    intro q a he hne
    rcases List.mem_append.mp he with he | he
    · exact he
    · exact absurd (congrArg Sigma.snd (List.mem_singleton.mp he)) hne
  have h₃' := old h₃ hd
  have h₂' := old h₂ fun hiv : iv = u ↦
    hu (hiv ▸ mem_inPlay_of_mem_halves h₃' (mem_halves_seedInput iv st.2))
  have h₁' := old h₁ fun hph : ph = u ↦
    hu (hph ▸ mem_inPlay_of_mem_programHashSlot h₂' (mem_programHashSlot_seedPreimageOf ph))
  exact ⟨ph, iv, h₁', h₂', h₃'⟩

/-- **Deduplication** changes no statement of a consistent log. -/
theorem stmtOf_dedupKeys (l : hashSpec.QueryLog) (hcons : QueryLog.Consistent l) (d : Digest) :
    stmtOf (List.dedupKeys l) d = stmtOf l d :=
  stmtOf_congr fun st ↦ by simp only [SeedLogged, QueryLog.mem_dedupKeys_iff hcons]

/-! ## No state past a start is a start -/

/-- **A state past a step is no start**: on a log with no collision, a state a logged step leads
to from a state that answers a 64-byte input opens no statement. -/
theorem stmtOf_eq_none_of_step {l : hashSpec.QueryLog} (hcoll : ¬ QueryLog.HasCollision l)
    {x y : Digest} {b : Block} (hstep : ⟨Block.input x b, y⟩ ∈ l) {q : List UInt8}
    (hq : q.length = 64) (hx : ⟨q, x⟩ ∈ l) : stmtOf l y = none := by
  refine stmtOf_eq_none fun st hst ↦ ?_
  obtain ⟨ph, iv, -, h₂, h₃⟩ := hst
  have hin := input_eq_of_noCollision hcoll h₃ hstep
  have hiv : iv = x := by
    have := congrArg digestOfBytes hin
    simpa [seedInput, Block.input, FsState.stepBytes, digestOfBytes_append] using this
  subst hiv
  have := congrArg List.length (input_eq_of_noCollision hcoll h₂ hx)
  rw [length_seedPreimageOf, hq] at this
  omega

/-- **No state of a chain from a first state is a start**: on a log with no collision holding
every step of a chain from a state that answers a 64-byte input, no later state of the chain opens
a statement. -/
theorem stmtOf_states_eq_none {l : hashSpec.QueryLog} (hcoll : ¬ QueryLog.HasCollision l) :
    ∀ {σ : Digest} {q : List UInt8}, q.length = 64 → ⟨q, σ⟩ ∈ l →
      ∀ {steps : List (Block × Digest)}, (∀ e ∈ HashChain.queries Block.input σ steps, e ∈ l) →
        ∀ x ∈ steps.map (·.2), stmtOf l x = none
  | _, _, _, _, [], _, _, hx => by simp at hx
  | σ, q, hq, hσ, (b, y) :: rest, hchain, x, hx => by
    have hstep : ⟨Block.input σ b, y⟩ ∈ l := hchain _ (by simp [HashChain.queries])
    rcases List.mem_cons.mp hx with rfl | hx
    · exact stmtOf_eq_none_of_step hcoll hstep hq hσ
    · exact stmtOf_states_eq_none hcoll (Block.length_input σ b) hstep
        (fun e he ↦ hchain e (by simp [HashChain.queries, he])) x hx

end
end LeanerVM.Protocol
