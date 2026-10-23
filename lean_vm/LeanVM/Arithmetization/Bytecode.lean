/-
  LeanVM.Arithmetization.Bytecode

  The sixteen-slot bytecode encoding of an instruction, its eleven-coordinate bus entry, and the
  decoder for canonical eleven-coordinate entries.
-/

module

public import LeanVM.Semantics.Lemmas

/-!
# The bytecode encoding

At leanVM pin `3375f7a137c50b803f3416f6466b5d4e0719708a`, transcribed from:

* specification §8.1 (`doc/leanvm/body/08-end-to-end-protocol.tex`): instruction `z` is sixteen
  `K` slots, the opcode in slot 3, the operands, immediate lanes and flags after it, zero
  elsewhere;
* `crates/leanvm_core/src/cpu/layout.rs:221-300` (`bytecode_columns`): the eleven public program
  columns, the opcode then ten operand slots, offsets as g-powers, a `SET` immediate as its three
  limbs, the `DEREF` store-mode flags and `KECCAK`'s layout flags as `0` or `1`, unused slots
  zero; `crates/leanvm_core/src/leaf.rs:739-768` stacks them at slots `3..14`
  (`BYTECODE_PUBLIC_SLOT = 3`);
* `crates/leanvm_core/src/cpu/isa.rs:58-75`: the `DEREF` store mode as the flag pair
  `(f_pc, f_fp)`, `cell = (0, 0)`, `pc = (1, 0)`, `fp = (0, 1)`.

`entry i` is the bus entry of an instruction, the row of `bytecode_columns`; `encodeSlots i` is
its sixteen-slot row, the entry at slots 3 to 13. Both are defined in `LeanVM.Spec.Isa`, since
the verifier receives a program through them; `decode`, here, consumes an eleven-coordinate
entry. It is exact: `decode v = some i ↔ v = entry i` (`decode_eq_some_iff`); on a `DEREF`
tuple with free flags it names the mode whose flags they are (`decode_deref_eq_some_iff`).
Unknown opcodes, invalid `DEREF` flag pairs, `KECCAK` layout flags other than `0` and `1`, and
nonzero spare entry coordinates decode to `none`. These results establish the canonical entry
boundary.

`Program` already contains typed `Instr` values, and `Program.fetch` looks them up by address;
it does not invoke this decoder. `encodeSlots` constructs sixteen-slot vectors, but this
module does not decode arbitrary sixteen-slot vectors or prove a raw-bytecode-to-`Program`
loading/correspondence theorem. Those interfaces require separate coverage or rejection proofs.

## Wrong readings excluded

* `SET_CONSTANT`'s `k₂` rides slot 7, coordinate 4 of the entry, the slot `DEREF` uses for
  `f_pc`; `KECCAK`'s ten operands ride slots 4 to 13 (`decode_entry` on every constructor).
* The flag pair `(1, 1)` decodes to nothing, and so does every pair that is not one of the
  three.
* A nonzero spare entry coordinate is not ignored. Each opcode table's bytecode tuple carries
  literal zeros in its spare coordinates (`_flushes_*`, `verifier.py:799-916`), and `decode`
  rejects a tuple that violates that opcode's canonical entry shape. This is an eleven-coordinate
  entry claim, not rejection by the typed program's address lookup.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## The store-mode flags -/

/-- The store mode of a flag pair, if it is one of the three. -/
def derefMode? (fpc ffp : K) : Option DerefMode :=
  if fpc = 0 ∧ ffp = 0 then some .cell
  else if fpc = 1 ∧ ffp = 0 then some .pc
  else if fpc = 0 ∧ ffp = 1 then some .fp
  else none

/-! ## The bus entry and the sixteen slots -/

/-! ## The decoder -/

/-- A `KECCAK` layout flag, if the word is `0` or `1`. -/
def flag? (a : K) : Option Bool :=
  if a = 0 then some false else if a = 1 then some true else none

/-- The opcode of a code, if it is one of the six. -/
def opcode? (a : K) : Option Opcode :=
  if a = Opcode.xor.code then some .xor
  else if a = Opcode.mulNative.code then some .mulNative
  else if a = Opcode.setConstant.code then some .setConstant
  else if a = Opcode.deref.code then some .deref
  else if a = Opcode.jump.code then some .jump
  else if a = Opcode.keccak.code then some .keccak
  else none

/-- The spare coordinates `5..10` of an entry are zero. -/
def Spare5 (v : Vector K 11) : Prop :=
  v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 ∧ v[8] = 0 ∧ v[9] = 0 ∧ v[10] = 0

instance (v : Vector K 11) : Decidable (Spare5 v) := by unfold Spare5; infer_instance

/-- Read an entry back as an instruction: the exact inverse of `entry` (`decode_eq_some_iff`);
`none` on an unknown opcode, on a flag pair that is no mode, on a layout flag that is neither `0`
nor `1`, or on a nonzero spare slot. -/
def decode (v : Vector K 11) : Option Instr :=
  match opcode? v[0] with
  | some .xor => if v[4] = 0 ∧ Spare5 v then some (.xor v[1] v[2] v[3]) else none
  | some .mulNative => if v[4] = 0 ∧ Spare5 v then some (.mulNative v[1] v[2] v[3]) else none
  | some .setConstant =>
      if Spare5 v then some (.setConstant v[1] (E.ofLimbs v[2] v[3] v[4])) else none
  | some .deref =>
      match derefMode? v[4] v[5] with
      | some mode =>
        if v[6] = 0 ∧ v[7] = 0 ∧ v[8] = 0 ∧ v[9] = 0 ∧ v[10] = 0 then
          some (.deref v[1] v[2] v[3] mode)
        else none
      | none => none
  | some .jump => if v[4] = 0 ∧ Spare5 v then some (.jump v[1] v[2] v[3]) else none
  | some .keccak =>
      match flag? v[9], flag? v[10] with
      | some inOdd, some outOdd => some (.keccak ![v[1], v[2], v[3], v[4]] v[5] v[6] v[7] v[8] inOdd outOdd)
      | _, _ => none
  | none => none

/-! ## Proof helpers -/

/-- A four-vector is its four entries. -/
private theorem vecCons_apply (om : Fin 4 → K) : ![om 0, om 1, om 2, om 3] = om := by
  funext i
  fin_cases i <;> rfl

/-! ## Load-bearing lemmas -/

/-- The flags of a mode decode to that mode. -/
theorem derefMode?_flags (m : DerefMode) :
    derefMode? (derefFlags m).1 (derefFlags m).2 = some m := by
  cases m <;> simp [derefMode?, derefFlags]

/-- A flag pair decodes to a mode exactly when it is that mode's flags. -/
theorem derefMode?_eq_some_iff {fpc ffp : K} {m : DerefMode} :
    derefMode? fpc ffp = some m ↔ (fpc, ffp) = derefFlags m := by
  constructor
  · intro h
    unfold derefMode? at h
    split_ifs at h with h1 h2 h3 <;> cases h
    · exact Prod.ext h1.1 h1.2
    · exact Prod.ext h2.1 h2.2
    · exact Prod.ext h3.1 h3.2
  · intro h
    cases m <;> simp only [derefFlags, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp [derefMode?]

/-- The code of an opcode decodes to that opcode. -/
theorem opcode?_code (o : Opcode) : opcode? o.code = some o := by
  cases o <;> simp [opcode?, Opcode.code_injective.eq_iff]

/-- A word decodes to an opcode exactly when it is that opcode's code. -/
theorem opcode?_eq_some_iff {a : K} {o : Opcode} : opcode? a = some o ↔ a = o.code := by
  constructor
  · intro h
    unfold opcode? at h
    split_ifs at h <;> cases h <;> assumption
  · rintro rfl
    exact opcode?_code o

/-- Slot 3 is the opcode. -/
theorem entry_getElem_zero (i : Instr) : (entry i)[0] = i.opcode.code := by
  cases i <;> rfl

/-- A flag decodes to itself. -/
theorem flag?_flagK (b : Bool) : flag? (flagK b) = some b := by
  cases b <;> simp [flag?, flagK]

/-- A word decodes to a flag exactly when it is that flag's word. -/
theorem flag?_eq_some_iff {a : K} {b : Bool} : flag? a = some b ↔ a = flagK b := by
  constructor
  · intro h
    unfold flag? at h
    split_ifs at h with h0 h1 <;> cases h
    · exact h0
    · exact h1
  · rintro rfl
    exact flag?_flagK b

/-- Every instruction's entry decodes to it. -/
theorem decode_entry (i : Instr) : decode (entry i) = some i := by
  cases i with
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    have h := vecCons_apply om
    simp [decode, entry, opcode?_code, h, flag?_flagK]
  | _ => simp [decode, entry, opcode?_code, derefMode?_flags, ofLimbs_limb, Spare5]

/-- `decode` is the exact inverse of `entry`: a vector decodes to an instruction only when it is
that instruction's entry. -/
theorem decode_eq_some_iff {v : Vector K 11} {i : Instr} : decode v = some i ↔ v = entry i := by
  constructor
  · intro h
    unfold decode at h
    rcases hop : opcode? v[0] with _ | op
    · rw [hop] at h
      cases h
    · rw [hop] at h
      rw [opcode?_eq_some_iff] at hop
      cases op <;> dsimp only at h
      case deref =>
        rcases hm : derefMode? v[4] v[5] with _ | mode
        · rw [hm] at h
          cases h
        · rw [hm] at h
          dsimp only at h
          rw [derefMode?_eq_some_iff, Prod.mk.injEq] at hm
          split_ifs at h with hz
          cases h
          obtain ⟨z6, z7, z8, z9, z10⟩ := hz
          refine Vector.ext fun j hj ↦ ?_
          interval_cases j <;> simp [entry, hop, hm.1, hm.2, z6, z7, z8, z9, z10]
      case keccak =>
        rcases h9 : flag? v[9] with _ | inOdd <;> rcases h10 : flag? v[10] with _ | outOdd <;>
          rw [h9, h10] at h <;> try cases h
        rw [flag?_eq_some_iff] at h9 h10
        refine Vector.ext fun j hj ↦ ?_
        interval_cases j <;> simp [entry, hop, h9, h10]
      all_goals
        split_ifs at h with hz
        cases h
        simp only [Spare5] at hz
        refine Vector.ext fun j hj ↦ ?_
        interval_cases j <;> simp [entry, hop, hz]
  · rintro rfl
    exact decode_entry i

/-- A vector decodes to nothing exactly when it is no instruction's entry. -/
theorem decode_eq_none_iff {v : Vector K 11} : decode v = none ↔ ∀ i, v ≠ entry i := by
  simp only [Option.eq_none_iff_forall_ne_some, ne_eq, decode_eq_some_iff]

/-- A `DEREF` tuple with free flags decodes exactly to the `DEREF` with its operands and the store
mode whose flags it carries; a pair that is no mode's decodes to nothing. -/
theorem decode_deref_eq_some_iff {o1 o2 o3 fpc ffp : K} {i : Instr} :
    decode #v[Opcode.deref.code, o1, o2, o3, fpc, ffp, 0, 0, 0, 0, 0] = some i ↔
      ∃ mode, i = .deref o1 o2 o3 mode ∧ (fpc, ffp) = derefFlags mode := by
  simp only [decode, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, opcode?_code, and_self, ite_true]
  constructor
  · intro h
    rcases hm : derefMode? fpc ffp with _ | mode
    · rw [hm] at h
      cases h
    · rw [hm, Option.some.injEq] at h
      exact ⟨mode, h.symm, derefMode?_eq_some_iff.mp hm⟩
  · rintro ⟨mode, rfl, hf⟩
    rw [derefMode?_eq_some_iff.mpr hf]

/-- Distinct instructions have distinct entries. -/
theorem entry_injective : Function.Injective entry := by
  intro i j h
  have hi := decode_entry i
  rw [h, decode_entry] at hi
  exact (Option.some.inj hi).symm

/-- The sixteen slots: the entry at slots 3 to 13, zero elsewhere (specification §8.1). -/
theorem encodeSlots_getElem (i : Instr) (j : ℕ) (hj : j < 16) :
    (encodeSlots i)[j] = if h : 3 ≤ j ∧ j < 14 then (entry i)[j - 3] else 0 := by
  interval_cases j <;> simp [encodeSlots]

end
end LeanVM.Arithmetization
