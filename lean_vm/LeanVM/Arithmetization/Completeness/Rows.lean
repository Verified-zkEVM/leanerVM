/-
  LeanVM.Arithmetization.Completeness.Rows

  The row of an instruction executed at a state: the table it belongs to, the raw row, and what
  it sends on the bus as a function of the state, the successor and the read counts.
-/

module

public import LeanVM.Arithmetization.Completeness.Messages

@[expose] public section

/-!
# The row of an executed instruction

The witness of `constraintCompleteness` writes one row per executed state, in the table of the
opcode the program holds there. `rowOf mem pc fp cnt rbc ins` is that row for the instruction `ins`
executed from `(pc, fp)` over the image `mem`: the typed row of `Arithmetization.Tables`
(`xorRowOf` and its siblings, with the `JUMP` table's honest local witnesses appended), as a raw
row. Its memory reads carry the counts `cnt 0, cnt 1, …` in the order the circuit reads them, and
its bytecode read the count `rbc`.

`sendsOf` is what any such row sends, in the shape every table shares (`Completeness.Messages`):
the state pull and push, the bytecode pull and push of `entry ins` at `pc`, and per read a
memory pull of `(addr, count, v)` and a push of `(addr, g·count, v)`. `readAddrs` lists the
cells an instruction reads, and the memory reads of the row are those cells with the limbs the
image holds there. The master lemma `rowOf_sends` says that if the instruction executes
from `(pc, fp)` to `next` then the row sends exactly `sendsOf` with `next`, and
`readAddrs_valid` that every cell it reads is an address of the image. Both are per table,
from the table's relation (`*_refines_iff`) and the closed forms of `Completeness.Messages`.

## Wrong readings excluded

* The messages carry the limbs the image holds, not the row's own formulas: the third read of an
  `XOR` row carries `v_A + v_B`, and that this is the word at `fp·o_C` is the execution's
  (`xor_refines_iff`), never the row's. A row for an instruction that does not execute sends
  something else, and the bus rejects it.
* The `DEREF` target cell is `p·o_2` for the pointer `p` the image holds at `fp·o_1`, not
  `fp·o_2`: its address is the one read that depends on another.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component)

/-! ## Reading a word back as limbs -/

/-- The limbs read back at an address that holds a word are the word's. -/
theorem MemImage.limbsAt_eq_of_read {κ : ℕ} {L : MemImage κ} {a : K} {v : E}
    (h : L.read a = some v) : L.limbsAt a = #v[v.limb 0, v.limb 1, v.limb 2] := by
  unfold MemImage.limbsAt
  rw [h]

/-- The three limbs of `E.ofLimbs`, one by one. -/
theorem limb0_ofLimbs (c0 c1 c2 : K) : (E.ofLimbs c0 c1 c2).limb 0 = c0 := rfl

/-- The second limb of `E.ofLimbs`. -/
theorem limb1_ofLimbs (c0 c1 c2 : K) : (E.ofLimbs c0 c1 c2).limb 1 = c1 := rfl

/-- The third limb of `E.ofLimbs`. -/
theorem limb2_ofLimbs (c0 c1 c2 : K) : (E.ofLimbs c0 c1 c2).limb 2 = c2 := rfl

/-! ## The messages -/

/-- The array a memory message `(addr, count, v)` flattens to. -/
def memMsgOf (a c : K) (v : Vector K 3) : Array K := #[a, c, v[0], v[1], v[2]]

/-- The array a bytecode message `(pc, count, entry)` flattens to. -/
def bcMsgOf (pc c : K) (e : Vector K 11) : Array K :=
  #[pc, c, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10]]

/-- What a row sends: the state pull `(pc, fp)` and push `next`, the bytecode pull of `e` at `pc`
with count `rbc` and the push with count `g·rbc`, then for each read `(addr, count, v)` the
memory pull and the memory push with count `g·count`, in the circuits' order. -/
def sendsOf (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 11)
    (reads : List (K × K × Vector K 3)) : List (String × Array K) :=
  [(StatePull.name, #[pc, fp]), (StatePush.name, #[next.pc, next.fp]),
    (BytecodePull.name, bcMsgOf pc rbc e), (BytecodePush.name, bcMsgOf pc (g * rbc) e)] ++
  reads.flatMap fun x ↦
    [(MemPull.name, memMsgOf x.1 x.2.1 x.2.2), (MemPush.name, memMsgOf x.1 (g * x.2.1) x.2.2)]

/-- A row circuit's sends are those of its main at the row variable. -/
theorem rowSends_mk {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit K Input Output) (env : Environment K) :
    rowSends ⟨c⟩ env =
      (((c.main (varFromOffset Input 0)).operations (size Input)).interactionValues env).map
        (fun i ↦ (i.channel.name, i.msg)) := rfl

/-! ## The cells an instruction reads -/

/-- The cells an instruction reads, in the order its row's reads carry them (the circuits'
order): the operand cells (for `KECCAK` the thirteen read, then the thirteen written), and for
`DEREF` the pointer cell `fp·o₁`, the pointer's target `p·o₂`
(`p` the low limb of the word at `fp·o₁`) and the local cell `fp·o₃`. -/
noncomputable def readAddrs {κ : ℕ} (mem : MemImage κ) (fp : K) : Instr → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (mem.limbsAt (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .keccak om otail ob8 ocap oout _ _ =>
      [fp * om 0,
        fp * om 1,
        fp * om 2,
        fp * om 3,
        fp * (g ^ 0 * otail),
        fp * (g ^ 1 * otail),
        fp * (g ^ 2 * otail),
        fp * (g ^ 3 * otail),
        fp * ob8,
        fp * (g ^ 0 * ocap),
        fp * (g ^ 1 * ocap),
        fp * (g ^ 2 * ocap),
        fp * (g ^ 3 * ocap),
        fp * (g ^ 0 * oout),
        fp * (g ^ 1 * oout),
        fp * (g ^ 2 * oout),
        fp * (g ^ 3 * oout),
        fp * (g ^ 4 * oout),
        fp * (g ^ 5 * oout),
        fp * (g ^ 6 * oout),
        fp * (g ^ 7 * oout),
        fp * (g ^ 8 * oout),
        fp * (g ^ 9 * oout),
        fp * (g ^ 10 * oout),
        fp * (g ^ 11 * oout),
        fp * (g ^ 12 * oout)]

/-- The reads of an instruction's row: each cell it reads, with its count (`cnt` at its position)
and the limbs the image holds there. -/
noncomputable def readsOf {κ : ℕ} (mem : MemImage κ) (fp : K) (cnt : ℕ → K) (ins : Instr) :
    List (K × K × Vector K 3) :=
  (readAddrs mem fp ins).mapIdx fun j a ↦ (a, cnt j, mem.limbsAt a)

/-! ## The six instructions -/

/-- The `XOR` row of an execution sends the `XOR` messages: the third read carries the limbs of
the word at `fp·o_C`, which the execution makes the sum. -/
theorem xor_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp oA oB oC : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.xor oA oB oC) = some next) (rA rB rC rbc : K)
    (data : ProverData K) :
    rowSends ⟨xorTable⟩
        (Environment.fromArray (rawRow (xorRowOf mem pc fp oA oB oC rA rB rC rbc)) data) =
      sendsOf pc fp next rbc (entry (.xor oA oB oC))
        [(fp * oA, rA, mem.limbsAt (fp * oA)), (fp * oB, rB, mem.limbsAt (fp * oB)),
          (fp * oC, rC, mem.limbsAt (fp * oC))] := by
  obtain ⟨⟨hA, hB⟩, hC, rfl⟩ := (xor_refines_iff _ _ _).mp (xorRowOf_refines hexec rA rB rC rbc)
  rw [rowSends_mk, xor_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [xorRowOf] at hC ⊢
  rw [add_limbs] at hC
  have hC' := MemImage.limbsAt_eq_of_read hC
  simp only [limb_ofLimbs] at hC'
  rw [hC']
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next]

/-- The `MUL_NATIVE` row of an execution sends the `MUL_NATIVE` messages: the third read carries
the limbs of the word at `fp·o_C`, which the execution makes the product. -/
theorem mul_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp oA oB oC : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.mulNative oA oB oC) = some next) (rA rB rC rbc : K)
    (data : ProverData K) :
    rowSends ⟨mulTable⟩
        (Environment.fromArray (rawRow (mulRowOf mem pc fp oA oB oC rA rB rC rbc)) data) =
      sendsOf pc fp next rbc (entry (.mulNative oA oB oC))
        [(fp * oA, rA, mem.limbsAt (fp * oA)), (fp * oB, rB, mem.limbsAt (fp * oB)),
          (fp * oC, rC, mem.limbsAt (fp * oC))] := by
  obtain ⟨⟨hA, hB⟩, hC, rfl⟩ := (mul_refines_iff _ _ _).mp (mulRowOf_refines hexec rA rB rC rbc)
  rw [rowSends_mk, mul_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [mulRowOf] at hC ⊢
  rw [mul_limbs] at hC
  have hC' := MemImage.limbsAt_eq_of_read hC
  simp only [limb_ofLimbs] at hC'
  rw [hC']
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next]

/-- The `SET_CONSTANT` row of an execution sends the `SET_CONSTANT` messages: its one read carries
the limbs of the immediate. -/
theorem set_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp o : K} {k : E} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.setConstant o k) = some next) (rc rbc : K)
    (data : ProverData K) :
    rowSends ⟨setTable⟩ (Environment.fromArray (rawRow (setRowOf pc fp o k rc rbc)) data) =
      sendsOf pc fp next rbc (entry (.setConstant o k)) [(fp * o, rc, mem.limbsAt (fp * o))] := by
  obtain ⟨hk, rfl⟩ := (set_refines_iff _ _ _).mp (setRowOf_refines hexec rc rbc)
  rw [rowSends_mk, set_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [setRowOf] at hk ⊢
  have hk' := MemImage.limbsAt_eq_of_read hk
  simp only [limb_ofLimbs, Vector.getElem_mk] at hk'
  rw [hk']
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next]

/-- The `DEREF` row of an execution sends the `DEREF` messages: the pointer cell carries
`(p, 0, 0)`, the target `p·o₂` the limbs of the mode's source, and the local cell its word. -/
theorem deref_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp o1 o2 o3 : K} {mode : DerefMode}
    {next : Regs K} (hexec : execute mem ⟨pc, fp⟩ (.deref o1 o2 o3 mode) = some next)
    (r1 r2 r3 rbc : K) (data : ProverData K) :
    rowSends ⟨derefTable⟩
        (Environment.fromArray (rawRow (derefRowOf mem pc fp o1 o2 o3 mode r1 r2 r3 rbc)) data) =
      sendsOf pc fp next rbc (entry (.deref o1 o2 o3 mode))
        [(fp * o1, r1, mem.limbsAt (fp * o1)),
          ((mem.limbsAt (fp * o1))[0] * o2, r2, mem.limbsAt ((mem.limbsAt (fp * o1))[0] * o2)),
          (fp * o3, r3, mem.limbsAt (fp * o3))] := by
  obtain ⟨mode', ⟨hflags, h1, h3⟩, h2, rfl⟩ :=
    (deref_refines_iff _ _ _).mp (derefRowOf_refines hexec r1 r2 r3 rbc)
  rw [rowSends_mk, deref_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [derefRowOf] at hflags h1 h3 h2 ⊢
  obtain ⟨h4, h5⟩ := Prod.ext_iff.mp hflags
  -- the pointer cell holds `(p, 0, 0)`
  have e1 := MemImage.limbsAt_eq_of_read h1
  simp only [limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs] at e1
  have e1' : (mem.limbsAt (fp * o1))[1] = 0 := by rw [e1]; rfl
  have e1'' : (mem.limbsAt (fp * o1))[2] = 0 := by rw [e1]; rfl
  -- the target cell holds the limbs of the mode's source
  have e2 := MemImage.limbsAt_eq_of_read h2
  rw [← storeCoords_eval, h4, h5] at e2
  simp only [limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs] at e2
  simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next, e1', e1'', e2]

/-- The indicator slot of a `JUMP` raw row is its second witness. -/
theorem jumpRaw_get_indicator (r : JumpRow K) (w b : K) (data : ProverData K) :
    (Environment.fromArray (jumpRaw r w b) data).get (size JumpRow + 1) = b := by
  show ((rawRow r ++ #[w, b])[size JumpRow + 1]?).getD 0 = b
  rw [Array.getElem?_append_right (by rw [rawRow_size]; omega), rawRow_size]
  simp

/-- The sends of a `JUMP` raw row, in closed form: the pushed successor reads the indicator `b`. -/
theorem jumpRaw_sends (r : JumpRow K) (w b : K) (data : ProverData K) :
    rowSends ⟨jumpTable⟩ (Environment.fromArray (jumpRaw r w b) data) =
      [(StatePull.name, #[r.pc, r.fp]),
       (StatePush.name, #[b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.jump.code, r.oc, r.od, r.of, 0, 0, 0, 0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.jump.code, r.oc, r.od, r.of, 0, 0, 0, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oc, r.rc, r.vcond, 0, 0]),
       (MemPush.name, #[r.fp * r.oc, g * r.rc, r.vcond, 0, 0]),
       (MemPull.name, #[r.fp * r.od, r.rd, r.vpc, 0, 0]),
       (MemPush.name, #[r.fp * r.od, g * r.rd, r.vpc, 0, 0]),
       (MemPull.name, #[r.fp * r.of, r.rf, r.vfp, 0, 0]),
       (MemPush.name, #[r.fp * r.of, g * r.rf, r.vfp, 0, 0])] :=
  jump_sends_gen (varFromOffset JumpRow 0) (Environment.fromArray (jumpRaw r w b) data)
    (size JumpRow) r (eval_rowVar_append r #[w, b] data) b (jumpRaw_get_indicator r w b data)

/-- The `JUMP` row of an execution, with its honest local witnesses, sends the `JUMP` messages:
the condition, destination and frame cells carry `(v, 0, 0)` for the words in `K` they hold, and
the pushed successor is the destination and frame when the condition is nonzero and the
fall-through otherwise. -/
theorem jump_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp oc od of : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.jump oc od of) = some next) (rc rd rf rbc : K)
    (data : ProverData K) :
    rowSends ⟨jumpTable⟩
        (Environment.fromArray
          (jumpRaw (jumpRowOf mem pc fp oc od of rc rd rf rbc)
            (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
            (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)) data) =
      sendsOf pc fp next rbc (entry (.jump oc od of))
        [(fp * oc, rc, mem.limbsAt (fp * oc)), (fp * od, rd, mem.limbsAt (fp * od)),
          (fp * of, rf, mem.limbsAt (fp * of))] := by
  obtain ⟨⟨hc, hd, hf⟩, hnext⟩ := (jump_refines_iff _ _ _).mp (jumpRowOf_refines hexec rc rd rf rbc)
  rw [jumpRaw_sends]
  simp only [jumpRowOf] at hc hd hf hnext ⊢
  have ec := MemImage.limbsAt_eq_of_read hc
  have ed := MemImage.limbsAt_eq_of_read hd
  have ef := MemImage.limbsAt_eq_of_read hf
  simp only [limb0_ofLimbs, limb1_ofLimbs, limb2_ofLimbs] at ec ed ef
  have ec1 : (mem.limbsAt (fp * oc))[1] = 0 := by rw [ec]; rfl
  have ec2 : (mem.limbsAt (fp * oc))[2] = 0 := by rw [ec]; rfl
  have ed1 : (mem.limbsAt (fp * od))[1] = 0 := by rw [ed]; rfl
  have ed2 : (mem.limbsAt (fp * od))[2] = 0 := by rw [ed]; rfl
  have ef1 : (mem.limbsAt (fp * of))[1] = 0 := by rw [ef]; rfl
  have ef2 : (mem.limbsAt (fp * of))[2] = 0 := by rw [ef]; rfl
  subst hnext
  by_cases h0 : (mem.limbsAt (fp * oc))[0] = 0
  · simp [sendsOf, memMsgOf, bcMsgOf, entry, Regs.next, h0, ec1, ec2, ed1, ed2, ef1, ef2]
  · simp [sendsOf, memMsgOf, bcMsgOf, entry, h0, ec1, ec2, ed1, ed2, ef1, ef2, add_assoc,
      CharTwo.add_self_eq_zero]

/-- A memory message is its address, its count, then its limbs. -/
theorem memMsgOf_eq (a c : K) (v : Vector K 3) : memMsgOf a c v = #[a, c] ++ v.toArray := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | [_, _, _], _ => rfl

/-- The limbs the image holds at an address that holds a cell of lanes. -/
theorem limbsAt_laneCells {κ : ℕ} {mem : MemImage κ} {a : K} {L : Fin 25 → K} {odd : Bool}
    {free : K} {c : Fin 13} (h : mem.read a = some (laneCells L odd free c)) :
    mem.limbsAt a = #v[laneLimb L free (cellLanes odd c).1, laneLimb L free (cellLanes odd c).2,
      0] := by
  rw [MemImage.limbsAt_eq_of_read h]
  simp [laneCells, limb_ofLimbs]

set_option maxHeartbeats 16000000 in
/-- The `KECCAK` row of an execution sends the `KECCAK` messages: each of the twenty-six cells
carries the limbs of its lanes in its layout and a zero third limb. -/
theorem keccak_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp : K} {om : Fin 4 → K}
    {otail ob8 ocap oout : K} {inOdd outOdd : Bool} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.keccak om otail ob8 ocap oout inOdd outOdd) = some next)
    (cnt : Vector K 26) (rbc : K) (data : ProverData K) :
    rowSends ⟨keccakTable⟩
        (Environment.fromArray (rawRow (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd
          cnt rbc)) data) =
      sendsOf pc fp next rbc (entry (.keccak om otail ob8 ocap oout inOdd outOdd))
        [(fp * om 0, cnt[0], mem.limbsAt (fp * om 0)),
          (fp * om 1, cnt[1], mem.limbsAt (fp * om 1)),
          (fp * om 2, cnt[2], mem.limbsAt (fp * om 2)),
          (fp * om 3, cnt[3], mem.limbsAt (fp * om 3)),
          (fp * (g ^ 0 * otail), cnt[4], mem.limbsAt (fp * (g ^ 0 * otail))),
          (fp * (g ^ 1 * otail), cnt[5], mem.limbsAt (fp * (g ^ 1 * otail))),
          (fp * (g ^ 2 * otail), cnt[6], mem.limbsAt (fp * (g ^ 2 * otail))),
          (fp * (g ^ 3 * otail), cnt[7], mem.limbsAt (fp * (g ^ 3 * otail))),
          (fp * ob8, cnt[8], mem.limbsAt (fp * ob8)),
          (fp * (g ^ 0 * ocap), cnt[9], mem.limbsAt (fp * (g ^ 0 * ocap))),
          (fp * (g ^ 1 * ocap), cnt[10], mem.limbsAt (fp * (g ^ 1 * ocap))),
          (fp * (g ^ 2 * ocap), cnt[11], mem.limbsAt (fp * (g ^ 2 * ocap))),
          (fp * (g ^ 3 * ocap), cnt[12], mem.limbsAt (fp * (g ^ 3 * ocap))),
          (fp * (g ^ 0 * oout), cnt[13], mem.limbsAt (fp * (g ^ 0 * oout))),
          (fp * (g ^ 1 * oout), cnt[14], mem.limbsAt (fp * (g ^ 1 * oout))),
          (fp * (g ^ 2 * oout), cnt[15], mem.limbsAt (fp * (g ^ 2 * oout))),
          (fp * (g ^ 3 * oout), cnt[16], mem.limbsAt (fp * (g ^ 3 * oout))),
          (fp * (g ^ 4 * oout), cnt[17], mem.limbsAt (fp * (g ^ 4 * oout))),
          (fp * (g ^ 5 * oout), cnt[18], mem.limbsAt (fp * (g ^ 5 * oout))),
          (fp * (g ^ 6 * oout), cnt[19], mem.limbsAt (fp * (g ^ 6 * oout))),
          (fp * (g ^ 7 * oout), cnt[20], mem.limbsAt (fp * (g ^ 7 * oout))),
          (fp * (g ^ 8 * oout), cnt[21], mem.limbsAt (fp * (g ^ 8 * oout))),
          (fp * (g ^ 9 * oout), cnt[22], mem.limbsAt (fp * (g ^ 9 * oout))),
          (fp * (g ^ 10 * oout), cnt[23], mem.limbsAt (fp * (g ^ 10 * oout))),
          (fp * (g ^ 11 * oout), cnt[24], mem.limbsAt (fp * (g ^ 11 * oout))),
          (fp * (g ^ 12 * oout), cnt[25], mem.limbsAt (fp * (g ^ 12 * oout)))] := by
  obtain ⟨⟨i, o, hi, ho, hb⟩, -, rfl⟩ :=
    (keccak_refines_iff _ _ _).mp (keccakRowOf_refines hexec cnt rbc)
  have hi' : i = inOdd := by
    have := congrArg flag? hi; simpa [keccakRowOf, flag?_flagK] using this.symm
  have ho' : o = outOdd := by
    have := congrArg flag? ho; simpa [keccakRowOf, flag?_flagK] using this.symm
  subst hi' ho'
  set R := keccakRowOf mem pc fp om otail ob8 ocap oout i o cnt rbc with hR
  have hRoms : R.oms = om := keccakRowOf_oms ..
  have hRf : R.fp = fp := rfl
  have hRt : R.otail = otail := rfl
  have hRb : R.ob8 = ob8 := rfl
  have hRc : R.ocap = ocap := rfl
  have hRo : R.oout = oout := rfl
  have hL0 : mem.limbsAt (fp * om 0) =
      #v[laneLimb R.inLanes R.free (cellLanes i 0).1, laneLimb R.inLanes R.free (cellLanes i 0).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨0, by decide⟩)
  have hL1 : mem.limbsAt (fp * om 1) =
      #v[laneLimb R.inLanes R.free (cellLanes i 1).1, laneLimb R.inLanes R.free (cellLanes i 1).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨1, by decide⟩)
  have hL2 : mem.limbsAt (fp * om 2) =
      #v[laneLimb R.inLanes R.free (cellLanes i 2).1, laneLimb R.inLanes R.free (cellLanes i 2).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨2, by decide⟩)
  have hL3 : mem.limbsAt (fp * om 3) =
      #v[laneLimb R.inLanes R.free (cellLanes i 3).1, laneLimb R.inLanes R.free (cellLanes i 3).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨3, by decide⟩)
  have hL4 : mem.limbsAt (fp * (g ^ 0 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 4).1, laneLimb R.inLanes R.free (cellLanes i 4).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨4, by decide⟩)
  have hL5 : mem.limbsAt (fp * (g ^ 1 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 5).1, laneLimb R.inLanes R.free (cellLanes i 5).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨5, by decide⟩)
  have hL6 : mem.limbsAt (fp * (g ^ 2 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 6).1, laneLimb R.inLanes R.free (cellLanes i 6).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨6, by decide⟩)
  have hL7 : mem.limbsAt (fp * (g ^ 3 * otail)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 7).1, laneLimb R.inLanes R.free (cellLanes i 7).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨7, by decide⟩)
  have hL8 : mem.limbsAt (fp * ob8) =
      #v[laneLimb R.inLanes R.free (cellLanes i 8).1, laneLimb R.inLanes R.free (cellLanes i 8).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨8, by decide⟩)
  have hL9 : mem.limbsAt (fp * (g ^ 0 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 9).1, laneLimb R.inLanes R.free (cellLanes i 9).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨9, by decide⟩)
  have hL10 : mem.limbsAt (fp * (g ^ 1 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 10).1, laneLimb R.inLanes R.free (cellLanes i 10).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨10, by decide⟩)
  have hL11 : mem.limbsAt (fp * (g ^ 2 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 11).1, laneLimb R.inLanes R.free (cellLanes i 11).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨11, by decide⟩)
  have hL12 : mem.limbsAt (fp * (g ^ 3 * ocap)) =
      #v[laneLimb R.inLanes R.free (cellLanes i 12).1, laneLimb R.inLanes R.free (cellLanes i 12).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.in_eq ⟨12, by decide⟩)
  have hL13 : mem.limbsAt (fp * (g ^ 0 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 0).1, laneLimb R.outLanes 0 (cellLanes o 0).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨0, by decide⟩)
  have hL14 : mem.limbsAt (fp * (g ^ 1 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 1).1, laneLimb R.outLanes 0 (cellLanes o 1).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨1, by decide⟩)
  have hL15 : mem.limbsAt (fp * (g ^ 2 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 2).1, laneLimb R.outLanes 0 (cellLanes o 2).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨2, by decide⟩)
  have hL16 : mem.limbsAt (fp * (g ^ 3 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 3).1, laneLimb R.outLanes 0 (cellLanes o 3).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨3, by decide⟩)
  have hL17 : mem.limbsAt (fp * (g ^ 4 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 4).1, laneLimb R.outLanes 0 (cellLanes o 4).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨4, by decide⟩)
  have hL18 : mem.limbsAt (fp * (g ^ 5 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 5).1, laneLimb R.outLanes 0 (cellLanes o 5).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨5, by decide⟩)
  have hL19 : mem.limbsAt (fp * (g ^ 6 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 6).1, laneLimb R.outLanes 0 (cellLanes o 6).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨6, by decide⟩)
  have hL20 : mem.limbsAt (fp * (g ^ 7 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 7).1, laneLimb R.outLanes 0 (cellLanes o 7).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨7, by decide⟩)
  have hL21 : mem.limbsAt (fp * (g ^ 8 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 8).1, laneLimb R.outLanes 0 (cellLanes o 8).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨8, by decide⟩)
  have hL22 : mem.limbsAt (fp * (g ^ 9 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 9).1, laneLimb R.outLanes 0 (cellLanes o 9).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨9, by decide⟩)
  have hL23 : mem.limbsAt (fp * (g ^ 10 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 10).1, laneLimb R.outLanes 0 (cellLanes o 10).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨10, by decide⟩)
  have hL24 : mem.limbsAt (fp * (g ^ 11 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 11).1, laneLimb R.outLanes 0 (cellLanes o 11).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨11, by decide⟩)
  have hL25 : mem.limbsAt (fp * (g ^ 12 * oout)) =
      #v[laneLimb R.outLanes 0 (cellLanes o 12).1, laneLimb R.outLanes 0 (cellLanes o 12).2, 0] := by
    simpa [hRoms, hRf, hRt, hRb, hRc, hRo, keccakInOffset] using limbsAt_laneCells (hb.out_eq ⟨12, by decide⟩)
  rw [rowSends_mk, keccak_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [sendsOf, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, memMsgOf_eq]
  rw [hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8, hL9, hL10, hL11, hL12, hL13, hL14, hL15, hL16, hL17, hL18, hL19, hL20, hL21, hL22, hL23, hL24, hL25]
  cases i <;> cases o <;> simp [hR, keccakRowOf, KeccakRow.inLanes, KeccakRow.outLanes, bcMsgOf, laneLimb, cellLanes,
    entry, Regs.next, flagK, CharTwo.add_self_eq_zero]

/-! ## Every cell an instruction reads is an address -/

/-- Every cell an executing instruction reads is an address of the image: the execution reads it
(`*_refines_iff`, the bindings and the result cell). -/
theorem readAddrs_valid {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : Instr} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) :
    ∀ a ∈ readAddrs mem fp ins, ∃ w, mem.read a = some w := by
  cases ins with
  | xor oA oB oC =>
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (xor_refines_iff _ _ _).mp (xorRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hA⟩, ⟨_, hB⟩, ⟨_, hC⟩]
  | mulNative oA oB oC =>
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (mul_refines_iff _ _ _).mp (mulRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hA⟩, ⟨_, hB⟩, ⟨_, hC⟩]
  | setConstant o k =>
    obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp (setRowOf_refines hexec 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a rfl
    exact ⟨_, hk⟩
  | deref o1 o2 o3 mode =>
    obtain ⟨mode', ⟨-, h1, h3⟩, h2, -⟩ :=
      (deref_refines_iff _ _ _).mp (derefRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩]
  | jump oc od of =>
    obtain ⟨⟨hc, hd, hf⟩, -⟩ := (jump_refines_iff _ _ _).mp (jumpRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hc⟩, ⟨_, hd⟩, ⟨_, hf⟩]
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    obtain ⟨input, output, hin, hout, -, -⟩ :=
      (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _).mp hexec
    intro a ha
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨0, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨1, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨2, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨3, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨4, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨5, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨6, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨7, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨8, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨9, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨10, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨11, by decide⟩⟩
    · exact ⟨_, by simpa [keccakInOffset] using hin ⟨12, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨0, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨1, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨2, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨3, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨4, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨5, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨6, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨7, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨8, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨9, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨10, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨11, by decide⟩⟩
    · exact ⟨_, by simpa using hout ⟨12, by decide⟩⟩

/-! ## The row of an instruction -/

/-- The table of each opcode, in the ensemble's order (`leanIsaEnsemble`). -/
def opComponent : Opcode → Component K
  | .xor => ⟨xorTable⟩
  | .mulNative => ⟨mulTable⟩
  | .setConstant => ⟨setTable⟩
  | .deref => ⟨derefTable⟩
  | .jump => ⟨jumpTable⟩
  | .keccak => ⟨keccakTable⟩

/-- The width of a raw row of each opcode's table: the row's columns, and for `JUMP` its two
local witnesses. -/
def opWidth : Opcode → ℕ
  | .xor => size XorRow
  | .mulNative => size MulRow
  | .setConstant => size SetRow
  | .deref => size DerefRow
  | .jump => size JumpRow + 2
  | .keccak => size KeccakRow

/-- The raw row of an instruction executed from `(pc, fp)` over the image `mem`: the typed row of
its table with the read counts `cnt` (positionally, in the order the circuit reads) and the
bytecode count `rbc`, and for `JUMP` the honest inverse and indicator of the condition. -/
noncomputable def rowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) :
    Instr → Array K
  | .xor oA oB oC => rawRow (xorRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .mulNative oA oB oC => rawRow (mulRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .setConstant o k => rawRow (setRowOf pc fp o k (cnt 0) rbc)
  | .deref o1 o2 o3 mode =>
      rawRow (derefRowOf mem pc fp o1 o2 o3 mode (cnt 0) (cnt 1) (cnt 2) rbc)
  | .jump oc od of =>
      jumpRaw (jumpRowOf mem pc fp oc od of (cnt 0) (cnt 1) (cnt 2) rbc)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)
  | .keccak om otail ob8 ocap oout inOdd outOdd =>
      rawRow (keccakRowOf mem pc fp om otail ob8 ocap oout inOdd outOdd (Vector.ofFn fun j ↦ cnt j)
        rbc)

/-- The raw row of an instruction has the width of its table. -/
theorem rowOf_size {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) (ins : Instr) :
    (rowOf mem pc fp cnt rbc ins).size = opWidth ins.opcode := by
  cases ins <;> simp [rowOf, opWidth, Instr.opcode, rawRow_size, jumpRaw]

/-- **The row of an executing instruction sends `sendsOf`.** If the instruction executes from
`(pc, fp)` to `next`, its row, in its table, sends the state step from `(pc, fp)` to `next`, the
bytecode read of its entry at `pc`, and the reads of the cells it reads with the counts `cnt`. -/
theorem rowOf_sends {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : Instr} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) (cnt : ℕ → K) (rbc : K)
    (data : ProverData K) :
    rowSends (opComponent ins.opcode)
        (Environment.fromArray (rowOf mem pc fp cnt rbc ins) data) =
      sendsOf pc fp next rbc (entry ins) (readsOf mem fp cnt ins) := by
  cases ins with
  | xor oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, xor_exec_sends hexec]
    simp [readsOf, readAddrs]
  | mulNative oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, mul_exec_sends hexec]
    simp [readsOf, readAddrs]
  | setConstant o k =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, set_exec_sends hexec]
    simp [readsOf, readAddrs]
  | deref o1 o2 o3 mode =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, deref_exec_sends hexec]
    simp [readsOf, readAddrs]
  | jump oc od of =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, jump_exec_sends hexec]
    simp [readsOf, readAddrs]
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, keccak_exec_sends hexec]
    simp [readsOf, readAddrs]

end LeanVM.Arithmetization
