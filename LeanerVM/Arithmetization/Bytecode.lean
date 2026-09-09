/-
  LeanerVM.Arithmetization.Bytecode

  The sixteen-slot bytecode encoding of an instruction, its eight-coordinate bus entry, and the
  decoder that reads the public program back.
-/

module

public import LeanerVM.Semantics.Instruction

/-!
# The bytecode encoding

leanISA roadmap Layer 4 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category B, transcribed from:

* specification §8.1 (`doc/leanvm/body/08-end-to-end-protocol.tex:4-24`): instruction `z` is
  sixteen `K` slots, the opcode in slot 3, the operands and immediate lanes in slots 4–10, zero
  elsewhere (`:8`); the table at `:12-23` gives every instruction's slots;
* specification §6.4 (`06-bus-interactions.tex:90`): a bytecode entry on the bus is the opcode
  plus seven operands, eight coordinates after the separator, the address, and the count; §5.1
  (`05-arithmetization.tex:12`): shorter tuples are zero-padded to the `m = 16` slots;
* `crates/lean_vm/src/cpu/layout.rs:229-290` (`bytecode_columns`): the eight public program
  columns `(opcode, o1, o2, o3, fpc, ffp, extra0, extra1)`, with `SET_CONSTANT`'s immediate
  lanes at `o2, o3, fpc` (`:252-271`) and `BLAKE2S`'s last four operands at `fpc, ffp, extra0,
  extra1` (`:267-287`); the seed and finalize blocks carry them at `:385-395`;
* `crates/lean_vm/src/cpu/isa.rs:58-79` and specification §7.4 (`07-instruction-tables.tex:76`):
  the `DEREF` store mode as the flag pair `(f_pc, f_fp)`, `cell = (0, 0)`, `pc = (1, 0)`,
  `fp = (0, 1)`.

`entry i` is the bus entry of an instruction, the row of `bytecode_columns`; `encodeSlots i` is
its sixteen-slot row of §8.1, the entry at slots 3–10; `decode` reads an entry back. `decode` is
exact: `decode v = some i ↔ v = entry i` (`decode_eq_some_iff`). A vector whose opcode is not
one of the six codes, whose `DEREF` flags are not one of the three pairs, or whose spare slots
are not zero is no instruction, and `Program.fetch` at its address fails. This is where flag
booleanity lives: in the public program, not in an AIR constraint (roadmap acceptance test 18).

## Wrong readings excluded

* `SET_CONSTANT`'s `k₂` rides slot 7, coordinate 4 of the entry, the slot `DEREF` uses for
  `f_pc`; `BLAKE2S`'s `o_{m₃}, o_cv, o_out, o_md` ride slots 7–10 (acceptance test 16;
  `decode_entry` on every constructor).
* The flag pair `(1, 1)` decodes to nothing, and so does every pair that is not one of the
  three (acceptance test 18).
* A nonzero spare slot is not ignored. Every table's bytecode tuple carries literal zeros in
  its spare coordinates (`tables.rs:486-491`, `:553-558`, `:636`, `:742-747`), so no row can
  pull such an entry; the decoder rejects it, and the semantics fetches nothing at its address.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

@[expose] public section

/-! ## The store-mode flags -/

/-- The `DEREF` store-mode flags `(f_pc, f_fp)`: `cell ↦ (0, 0)`, `pc ↦ (1, 0)`, `fp ↦ (0, 1)`
(`isa.rs:69-78`; specification §7.4). -/
def derefFlags : DerefMode → K × K
  | .cell => (0, 0)
  | .pc => (1, 0)
  | .fp => (0, 1)

/-- The store mode of a flag pair, if it is one of the three (acceptance test 18). -/
def derefMode? (fpc ffp : K) : Option DerefMode :=
  if fpc = 0 ∧ ffp = 0 then some .cell
  else if fpc = 1 ∧ ffp = 0 then some .pc
  else if fpc = 0 ∧ ffp = 1 then some .fp
  else none

/-! ## The bus entry and the sixteen slots -/

/-- The bus entry of an instruction, `(opcode, op₁, …, op₇)`: slots 3–10 of specification §8.1,
the eight public columns of `layout.rs:229-290`. -/
def entry : Instr → Vector K 8
  | .xor oA oB oC => #v[Opcode.xor.code, oA, oB, oC, 0, 0, 0, 0]
  | .mulNative oA oB oC => #v[Opcode.mulNative.code, oA, oB, oC, 0, 0, 0, 0]
  | .setConstant o k => #v[Opcode.setConstant.code, o, k.limb 0, k.limb 1, k.limb 2, 0, 0, 0]
  | .deref o1 o2 o3 mode =>
      #v[Opcode.deref.code, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2, 0, 0]
  | .jump oc od of => #v[Opcode.jump.code, oc, od, of, 0, 0, 0, 0]
  | .blake2s om ocv oout omd => #v[Opcode.blake2s.code, om 0, om 1, om 2, om 3, ocv, oout, omd]

/-- The sixteen slots of an instruction (specification §8.1): the entry at slots 3–10, zero
elsewhere. -/
def encodeSlots (i : Instr) : Vector K 16 :=
  let e := entry i
  #v[0, 0, 0, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], 0, 0, 0, 0, 0]

/-! ## The decoder -/

/-- The opcode of a code, if it is one of the six. -/
def opcode? (a : K) : Option Opcode :=
  if a = Opcode.xor.code then some .xor
  else if a = Opcode.mulNative.code then some .mulNative
  else if a = Opcode.setConstant.code then some .setConstant
  else if a = Opcode.deref.code then some .deref
  else if a = Opcode.jump.code then some .jump
  else if a = Opcode.blake2s.code then some .blake2s
  else none

/-- Read an entry back as an instruction: the exact inverse of `entry` (`decode_eq_some_iff`);
`none` on an unknown opcode, on a flag pair that is no mode, or on a nonzero spare slot. -/
def decode (v : Vector K 8) : Option Instr :=
  match opcode? v[0] with
  | some .xor =>
      if v[4] = 0 ∧ v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.xor v[1] v[2] v[3]) else none
  | some .mulNative =>
      if v[4] = 0 ∧ v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.mulNative v[1] v[2] v[3])
      else none
  | some .setConstant =>
      if v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.setConstant v[1] (E.ofLimbs v[2] v[3] v[4]))
      else none
  | some .deref =>
      match derefMode? v[4] v[5] with
      | some mode => if v[6] = 0 ∧ v[7] = 0 then some (.deref v[1] v[2] v[3] mode) else none
      | none => none
  | some .jump =>
      if v[4] = 0 ∧ v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.jump v[1] v[2] v[3]) else none
  | some .blake2s => some (.blake2s ![v[1], v[2], v[3], v[4]] v[5] v[6] v[7])
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

/-- Every instruction's entry decodes to it (acceptance test 16). -/
theorem decode_entry (i : Instr) : decode (entry i) = some i := by
  cases i with
  | blake2s om ocv oout omd =>
    have h := vecCons_apply om
    simp [decode, entry, opcode?_code, h]
  | _ => simp [decode, entry, opcode?_code, derefMode?_flags, ofLimbs_limb]

/-- `decode` is the exact inverse of `entry`: a vector decodes to an instruction only when it is
that instruction's entry. -/
theorem decode_eq_some_iff {v : Vector K 8} {i : Instr} : decode v = some i ↔ v = entry i := by
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
          refine Vector.ext fun j hj ↦ ?_
          interval_cases j <;> simp [entry, hop, hm.1, hm.2, hz.1, hz.2]
      all_goals
        first
        | (split_ifs at h with hz
           cases h
           refine Vector.ext fun j hj ↦ ?_
           interval_cases j <;> simp [entry, hop, hz])
        | (cases h
           refine Vector.ext fun j hj ↦ ?_
           interval_cases j <;> simp [entry, hop])
  · rintro rfl
    exact decode_entry i

/-- A vector decodes to nothing exactly when it is no instruction's entry. -/
theorem decode_eq_none_iff {v : Vector K 8} : decode v = none ↔ ∀ i, v ≠ entry i := by
  simp only [Option.eq_none_iff_forall_ne_some, ne_eq, decode_eq_some_iff]

/-- Distinct instructions have distinct entries. -/
theorem entry_injective : Function.Injective entry := by
  intro i j h
  have hi := decode_entry i
  rw [h, decode_entry] at hi
  exact (Option.some.inj hi).symm

/-- The sixteen slots: the entry at slots 3–10, zero elsewhere (specification §8.1). -/
theorem encodeSlots_getElem (i : Instr) (j : ℕ) (hj : j < 16) :
    (encodeSlots i)[j] = if h : 3 ≤ j ∧ j < 11 then (entry i)[j - 3] else 0 := by
  interval_cases j <;> simp [encodeSlots]

end
end LeanerVM.Arithmetization
