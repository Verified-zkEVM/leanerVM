/-
  LeanVM.Guest.B2C.CountB

  Counted runs (`Count.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.Count
public import LeanVM.Guest.B2C.SemDeployed

/-!
# Counted runs under any `BLAKE2S` semantics

`Count.lean`'s counted runs over the run under `S : BlakeSem` (`runB S`): `runCountB S` counts
the instructions of each opcode as `runB S` steps (`runCount` under `S`), `RunCB S` is a counted
run, and the lemmas are proved as there: `RunCB.trans`, `runCB_step`, `runCB_fallThrough`,
`runCB_jump`, `runCB_jumpTo`, `runCB_ret`, `runB_final_unique`, `countB_eq_of_runC` (the count is
`runCountB S` of the halting run), `LeavesCB`, `ReachCB`, `SegGoodCB` and the executor's
completeness, counted (`execB_completeC`, `execWinB_completeC`). `runB_zero`,
`stepB_eq_none_of_fetch_eq_none`, `pc_ne_finalPc_of_runB_succ` are `Semantics/Lemmas.lean`'s
under `S`.

* `runCountB_deployed`, `runCB_deployed`, `reachCB_deployed`, `leavesCB_deployed`,
  `segGoodCB_deployed`: at `blakeDeployed`, they are `Count.lean`'s (and `runCount`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Exec

@[expose] public section

variable {S : BlakeSem}

/-! ## Runs and counts under `S` -/

/-- The number of instructions of opcode `op` executed in `n` steps from `r` under `S`, stepping
as `runB S` does (`runCount` under `S`); the count stops at a step that fails. -/
noncomputable def runCountB (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ)
    (op : Opcode) : ℕ → Regs K → ℕ
  | 0, _ => 0
  | n + 1, r =>
    match prog.fetch r.pc, stepB S prog L r with
    | some ins, some r' => (if ins.opcode = op then 1 else 0) + runCountB S prog L op n r'
    | _, _ => 0

section RunB

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

@[simp] theorem runB_zero (r : Regs K) : runB S prog L 0 r = some r := rfl

/-- A counter that fetches nothing steps nowhere. -/
theorem stepB_eq_none_of_fetch_eq_none {r : Regs K} (h : prog.fetch r.pc = none) :
    stepB S prog L r = none := by
  rw [stepB, h]; rfl

/-- A run that takes a step starts away from the sentinel. -/
theorem pc_ne_finalPc_of_runB_succ {n : ℕ} {r r' : Regs K}
    (h : runB S prog L (n + 1) r = some r') : r.pc ≠ prog.finalPc :=
  fun hpc ↦ by rw [runB_succ_of_eq hpc] at h; exact Option.some_ne_none r' h.symm

end RunB

/-! ## Counted runs -/

variable (S) in
/-- **A counted run**: some run goes from `s` to `t`, executing `c op` instructions of each
opcode `op`. -/
def RunCB {κ : ℕ} (prog : Program) (L : MemImage κ) (s t : Regs K) (c : Opcode → ℕ) : Prop :=
  ∃ n, runB S prog L n s = some t ∧ ∀ op, runCountB S prog L op n s = c op

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

/-- Along a run that reaches `t`, the counts of a longer run add. -/
theorem runCountB_add_of_run {op : Opcode} : ∀ {n : ℕ} {s t : Regs K}, runB S prog L n s = some t →
    ∀ m, runCountB S prog L op (n + m) s = runCountB S prog L op n s + runCountB S prog L op m t
  | 0, s, t, h, m => by
    simp only [runB_zero, Option.some.injEq] at h
    subst h
    simp [runCountB]
  | n + 1, s, t, h, m => by
    have hne := pc_ne_finalPc_of_runB_succ h
    rw [runB_succ_of_ne hne] at h
    obtain ⟨s', hs', h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ins, hins⟩ : ∃ ins, prog.fetch s.pc = some ins := by
      cases hf : prog.fetch s.pc with
      | none => rw [stepB_eq_none_of_fetch_eq_none hf] at hs'; cases hs'
      | some ins => exact ⟨ins, rfl⟩
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [runCountB, hins, hs', runCountB_add_of_run h' m]
    omega

theorem RunCB.refl (s : Regs K) : RunCB S prog L s s 0 := ⟨0, rfl, fun _ ↦ rfl⟩

theorem RunCB.trans {s t u : Regs K} {c₁ c₂ : Opcode → ℕ} (h₁ : RunCB S prog L s t c₁)
    (h₂ : RunCB S prog L t u c₂) : RunCB S prog L s u (c₁ + c₂) := by
  obtain ⟨m, hm, hcm⟩ := h₁
  obtain ⟨n, hn, hcn⟩ := h₂
  refine ⟨m + n, by rw [runB_add, hm]; exact hn, fun op ↦ ?_⟩
  rw [runCountB_add_of_run hm, hcm, hcn, Pi.add_apply]

theorem RunCB.reach {s t : Regs K} {c : Opcode → ℕ} (h : RunCB S prog L s t c) : ReachB S prog L s t :=
  let ⟨n, hn, _⟩ := h
  ⟨n, hn⟩

/-! ## Counted steps -/

/-- One step from a fetched instruction away from the last slot, counting its opcode. -/
theorem runCB_step {pc : ℕ} {fp : K} {ins : OInstr} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (h : executeB S L ⟨gpow pc, fp⟩ ins.toInstr = some r) :
    RunCB S prog L ⟨gpow pc, fp⟩ r (fun op ↦ if op = ins.toInstr.opcode then 1 else 0) := by
  have hf' : prog.fetch (⟨gpow pc, fp⟩ : Regs K).pc = some ins.toInstr := hf
  have hs : stepB S prog L ⟨gpow pc, fp⟩ = some r := by rw [stepB_of_fetch_eq_some hf', h]
  refine ⟨1, ?_, fun op ↦ ?_⟩
  · rw [runB_succ_of_ne (gpow_ne_finalPc hpc), hs]
    rfl
  · simp only [runCountB, hf', hs, add_zero]
    by_cases ho : op = ins.toInstr.opcode
    · simp [ho]
    · simp [ho, Ne.symm ho]

/-- A non-`JUMP` that `HoldsB` falls through, counting its opcode. -/
theorem runCB_fallThrough {pc : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (hj : ins.isJump = false) (h : HoldsB S L pc fp ins) :
    RunCB S prog L ⟨gpow pc, fp⟩ ⟨gpow (pc + 1), fp⟩ (fun op ↦ if op = ins.toInstr.opcode then 1 else 0) :=
  runCB_step hf hpc ((executeB_iff_holds hj).mpr ⟨h, rfl⟩)

/-- A `JUMP` goes where it `JumpsTo`, counting one `JUMP`. -/
theorem runCB_jump {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : JumpsTo L pc fp oc od of r) :
    RunCB S prog L ⟨gpow pc, fp⟩ r (fun op ↦ if op = .jump then 1 else 0) :=
  runCB_step hf hpc (executeB_jump_iff.mpr h)

/-- A taken `JUMP` whose target cells hold `a` and `b` goes to `(a, b)`, counting one `JUMP`. -/
theorem runCB_jumpTo {pc oc od of : ℕ} {fp a b : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hcK : IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * gpow od) = some (ofK a))
    (hf' : L.read (fp * gpow of) = some (ofK b)) :
    RunCB S prog L ⟨gpow pc, fp⟩ ⟨a, b⟩ (fun op ↦ if op = .jump then 1 else 0) := by
  have hK : ∀ x : K, IsInK (ofK x) := fun x ↦ (isInK_iff _).mpr ⟨x, rfl⟩
  have hr : (if c = 0 then (⟨gpow (pc + 1), fp⟩ : Regs K) else ⟨(ofK a).limb 0, (ofK b).limb 0⟩) =
      ⟨a, b⟩ := by
    rw [ite_eq_right hc0]
    simp
  exact runCB_jump hf hpc ⟨c, _, _, hc, hd, hf', hcK, hK a, hK b, hr.symm⟩

/-- A return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc]` a nonzero `K` word and `fp[0]`, `fp[1]`
words of `K`, goes to `retRegs L fp`, counting one `JUMP`. -/
theorem runCB_ret {pc oc : ℕ} {fp : K} {c d f : E} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc 0 1).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hcK : IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * gpow 0) = some d) (hdK : IsInK d)
    (hf' : L.read (fp * gpow 1) = some f) (hfK : IsInK f) (hr : retRegs L fp = some r) :
    RunCB S prog L ⟨gpow pc, fp⟩ r (fun op ↦ if op = .jump then 1 else 0) := by
  obtain ⟨d', f', hd', hf'', rfl⟩ := retRegs_eq_some_iff.mp hr
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f' = f := Option.some.inj (hf''.symm.trans hf')
  exact runCB_jump hf hpc ⟨c, d', f', hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩

/-! ## The final registers -/

/-- A run reaches the final registers after one number of steps only: it halts there. -/
theorem runB_final_unique {n m : ℕ} {s : Regs K} (hn : runB S prog L n s = some (Regs.final prog))
    (hm : runB S prog L m s = some (Regs.final prog)) : n = m := by
  have key : ∀ {a b : ℕ}, a < b → runB S prog L a s = some (Regs.final prog) →
      runB S prog L b s ≠ some (Regs.final prog) := by
    intro a b hab ha hb
    obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
    rw [runB_add, ha] at hb
    change runB S prog L (k + 1) (Regs.final prog) = _ at hb
    rw [runB_succ_of_eq rfl] at hb
    cases hb
  rcases Nat.lt_trichotomy n m with h | h | h
  · exact absurd hm (key h hn)
  · exact h
  · exact absurd hn (key h hm)

/-- **A counted run to the final registers counts the trace that halts there.** -/
theorem countB_eq_of_runC {n : ℕ} {c : Opcode → ℕ}
    (hc : RunCB S prog L Regs.initial (Regs.final prog) c)
    (hn : runB S prog L n Regs.initial = some (Regs.final prog)) (op : Opcode) :
    runCountB S prog L op n Regs.initial = c op := by
  obtain ⟨m, hm, hcm⟩ := hc
  obtain rfl := runB_final_unique hn hm
  exact hcm op

end

/-! ## The pass, counted -/

section Pass

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {entry len : ℕ}

variable (S) in
/-- A counted run from `s` to `r` within the instructions of `its`, by an exit `x` with `X x`
whose kind names `r` and whose environment holds. -/
def LeavesCB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (s r : Regs K) (its : List Item)
    (X : Exit → Prop) : Prop :=
  ∃ c, RunCB S prog L s r c ∧ (∀ op, c op ≤ itemOps its op) ∧
    ∃ x, X x ∧ x.kind.Regs L fp entry r ∧ EnvHolds L fp x.env

variable (S) in
/-- A counted run from `s` to `t` within the instructions of `its`. -/
def ReachCB (L : MemImage κ) (prog : Program) (s t : Regs K) (its : List Item) : Prop :=
  ∃ c, RunCB S prog L s t c ∧ ∀ op, c op ≤ itemOps its op

private theorem LeavesCB.prefix {s r : Regs K} {l₁ l₂ : List Item} {X Y : Exit → Prop}
    (hXY : ∀ x, X x → Y x) (h : LeavesCB S L fp prog entry s r l₁ X) :
    LeavesCB S L fp prog entry s r (l₁ ++ l₂) Y := by
  obtain ⟨c, hc, hle, x, hx, hr, he⟩ := h
  exact ⟨c, hc, fun op ↦ (hle op).trans (by rw [itemOps_append]; omega), x, hXY x hx, hr, he⟩

private theorem LeavesCB.after {s t r : Regs K} {l₁ l₂ : List Item} {X Y : Exit → Prop}
    (hXY : ∀ x, X x → Y x) (h₁ : ReachCB S L prog s t l₁) (h : LeavesCB S L fp prog entry t r l₂ X) :
    LeavesCB S L fp prog entry s r (l₁ ++ l₂) Y := by
  obtain ⟨c₁, hc₁, hle₁⟩ := h₁
  obtain ⟨c, hc, hle, x, hx, hr, he⟩ := h
  refine ⟨c₁ + c, hc₁.trans hc, fun op ↦ ?_, x, hXY x hx, hr, he⟩
  rw [Pi.add_apply, itemOps_append]
  exact Nat.add_le_add (hle₁ op) (hle op)

private theorem ReachCB.trans {s t u : Regs K} {l₁ l₂ : List Item} (h₁ : ReachCB S L prog s t l₁)
    (h₂ : ReachCB S L prog t u l₂) : ReachCB S L prog s u (l₁ ++ l₂) := by
  obtain ⟨c₁, hc₁, hle₁⟩ := h₁
  obtain ⟨c₂, hc₂, hle₂⟩ := h₂
  refine ⟨c₁ + c₂, hc₁.trans hc₂, fun op ↦ ?_⟩
  rw [Pi.add_apply, itemOps_append]
  exact Nat.add_le_add (hle₁ op) (hle₂ op)

variable (S) in
/-- What an instruction's result gives a run to `r`, counted: from its atoms, the run reaches `r`
by a branch's exit, or the next offset with `Q`; or, when it stops, `r` by its exit. -/
private def ResCompCB (L : MemImage κ) (fp : K) (prog : Program) (entry i : ℕ) (r : Regs K) :
    Res → Prop
  | .go its st => ∀ Q : Prop, FollowsB S L fp entry r Q its →
      LeavesCB S L fp prog entry ⟨gpow (entry + i), fp⟩ r its (· ∈ branchExits its) ∨
        (Q ∧ St.HoldsB S L fp st ∧ ReachCB S L prog ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩ its)
  | .stop its x => FollowsB S L fp entry r (x.kind.Regs L fp entry r) its →
      LeavesCB S L fp prog entry ⟨gpow (entry + i), fp⟩ r its (fun y ↦ y = x ∨ y ∈ branchExits its)

private theorem itemOps_ins_facts (a : Atom) (fs : List Atom) (op : Opcode) :
    itemOp (.ins a) op ≤ itemOps (.ins a :: fs.map .fact) op := by
  rw [itemOps_cons]
  exact Nat.le_add_right _ _

/-- **One instruction is complete, counted.** -/
private theorem stepIB_completeC (hctx : Ctx F κ fp) {i : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.HoldsB S L fp st) (r : Regs K) :
    ResCompCB S L fp prog entry i r (stepI F entry len i st ins) := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    rintro Q ⟨hh, hq⟩
    rw [followsB_facts] at hq
    obtain ⟨-, he, hm⟩ := nonJumpB_holds hctx.le hctx.pows hst hh
    exact Or.inr ⟨hq, hst.push he hm hh, _, runCB_fallThrough hf hpc hj hh,
      fun op ↦ itemOps_ins_facts (.instr (entry + i) ins) _ op⟩
  | true =>
    cases ins with
    | jump oc od of =>
      have hone : ∀ (a : Item), (∀ op, itemOp a op = if op = .jump then 1 else 0) →
          ∀ op, (if op = Opcode.jump then 1 else 0) ≤ itemOps [a] op := by
        intro a ha op
        rw [itemOps_cons, itemOps_nil, ha]
        exact Nat.le_add_right _ _
      have hgo : ∀ {c d f : E}, L.read (fp * gpow oc) = some c → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK c → IsInK d → IsInK f → c ≠ 0 →
          (jumpExit F entry len i st od of).kind.Regs L fp entry r →
          RunCB S prog L ⟨gpow (entry + i), fp⟩ r (fun op ↦ if op = .jump then 1 else 0) ∧
            EnvHolds L fp (jumpExit F entry len i st od of).env := by
        intro c d f hc hd hf' hcK hdK hfK hc0 hr
        obtain ⟨hreg, -⟩ := jumpKindB_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst
          hd hdK hf' hfK
        rw [jumpExit_eq] at hr ⊢
        obtain rfl := Kind.regs_unique hr hreg
        exact ⟨runCB_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩,
          hst.1⟩
      have hnext : ∀ {d f : E}, L.read (fp * gpow oc) = some 0 → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK d → IsInK f →
          RunCB S prog L ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩
            (fun op ↦ if op = .jump then 1 else 0) := by
        intro d f hc hd hf' hdK hfK
        exact runCB_jump hf hpc ⟨0, d, f, hc, hd, hf', (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩, hdK,
          hfK, by rw [ite_eq_left rfl]⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', -, hdK, hfK⟩, hq⟩
        have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        exact Or.inr ⟨hq, hst, _, hnext hc hd hf' hdK hfK, hone _ fun _ ↦ rfl⟩
      · rintro ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, hr⟩
        obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        obtain ⟨hrun, he⟩ := hgo hc hd hf' hcK hdK hfK (hcw ▸ hw0) hr
        exact ⟨_, hrun, hone _ fun _ ↦ rfl, _, Or.inl rfl, hr, he⟩
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, ⟨h0, hq⟩ | ⟨⟨v, hv, hv0⟩, hr⟩⟩
        · obtain rfl : c = 0 := Option.some.inj (hc.symm.trans h0)
          exact Or.inr ⟨hq, hst, _, hnext hc hd hf' hdK hfK, hone _ fun _ ↦ rfl⟩
        · obtain rfl := Option.some.inj (hv.symm.trans hc)
          obtain ⟨hrun, he⟩ := hgo hc hd hf' hcK hdK hfK hv0 hr
          exact Or.inl ⟨_, hrun, hone _ fun _ ↦ rfl, _, List.mem_singleton_self _, hr, he⟩
    | _ => simp [OInstr.isJump] at hj

variable (S) in
/-- A segment being walked, at offset `i`, complete with counts. -/
private def CurGoodCB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (c : Cur) (i : ℕ) :
    Prop :=
  EnvHolds L fp c.env → ∀ r Q, FollowsB S L fp entry r Q c.acc.reverse →
    LeavesCB S L fp prog entry ⟨gpow (entry + c.start), fp⟩ r c.acc.reverse
        (· ∈ branchExits c.acc.reverse) ∨
      (Q ∧ St.HoldsB S L fp c.st ∧
        ReachCB S L prog ⟨gpow (entry + c.start), fp⟩ ⟨gpow (entry + i), fp⟩ c.acc.reverse)

variable (S) in
/-- A segment, complete with counts and its exit. -/
def SegGoodCB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (s : Seg) : Prop :=
  EnvHolds L fp s.env → ∀ r, FollowsB S L fp entry r (s.exit.kind.Regs L fp entry r) s.items →
    LeavesCB S L fp prog entry ⟨gpow (entry + s.start), fp⟩ r s.items
      (fun x ↦ x = s.exit ∨ x ∈ branchExits s.items)

private theorem curGoodCB_init (i : ℕ) (env : Trie Sym) :
    CurGoodCB S L fp prog entry (Cur.init i env) i :=
  fun he _ _ hq ↦ Or.inr ⟨hq, stHoldsB_init he, 0, RunCB.refl _, fun _ ↦ Nat.zero_le _⟩

private theorem segGoodCB_close {c : Cur} {i : ℕ} (hc : CurGoodCB S L fp prog entry c i)
    (succ : List ℕ) : SegGoodCB S L fp prog entry (c.close [] ⟨.next i, c.st.env, succ⟩) := by
  intro he r hf
  simp only [Cur.close, items_close, List.append_nil] at hf ⊢
  rcases hc he r _ hf with ⟨n, hn, hle, x, hx, hr, hxe⟩ | ⟨rfl, hst, n, hn, hle⟩
  · exact ⟨n, hn, hle, x, Or.inr hx, hr, hxe⟩
  · exact ⟨n, hn, hle, _, Or.inl rfl, rfl, hst.1⟩

private theorem curGoodCB_go (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurGoodCB S L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {st : St}
    (hs : stepI F entry len i c.st ins = .go its st) :
    CurGoodCB S L fp prog entry
      ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩ (i + 1) := by
  intro he r Q hq
  simp only [List.reverseAux_eq, List.reverse_append, List.reverse_reverse] at hq ⊢
  have hmem : ∀ l₁ l₂ : List Item, ∀ x, x ∈ branchExits l₁ ∨ x ∈ branchExits l₂ →
      x ∈ branchExits (l₁ ++ l₂) := fun l₁ l₂ x hx ↦ by
    rw [branchExits_append]
    exact List.mem_append.mpr hx
  rcases hc he r _ (FollowsB.append hq) with h | ⟨hq', hst, h⟩
  · exact Or.inl (h.prefix fun x hx ↦ hmem _ _ x (Or.inl hx))
  · have := stepIB_completeC (len := len) hctx hf hpc hst r
    rw [hs] at this
    rcases this Q hq' with h' | ⟨hQ, hst', h'⟩
    · exact Or.inl (LeavesCB.after (fun x hx ↦ hmem _ _ x (Or.inr hx)) h h')
    · refine Or.inr ⟨hQ, hst', ?_⟩
      have e : entry + i + 1 = entry + (i + 1) := by omega
      rw [e] at h'
      exact h.trans h'

private theorem segGoodCB_stop (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurGoodCB S L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {x : Exit}
    (hs : stepI F entry len i c.st ins = .stop its x) : SegGoodCB S L fp prog entry (c.close its x) := by
  intro he r hq
  simp only [Cur.close, items_close] at hq ⊢
  have hmem : ∀ y, y ∈ branchExits c.acc.reverse ∨ y ∈ branchExits its →
      y ∈ branchExits (c.acc.reverse ++ its) := fun y hy ↦ by
    rw [branchExits_append]
    exact List.mem_append.mpr hy
  rcases hc he r _ (FollowsB.append hq) with h | ⟨hq', hst, h⟩
  · exact h.prefix fun y hy ↦ Or.inr (hmem y (Or.inl hy))
  · have := stepIB_completeC (len := len) hctx hf hpc hst r
    rw [hs] at this
    exact LeavesCB.after (fun y hy ↦ hy.imp id fun hy ↦ hmem y (Or.inr hy)) h (this hq')

private theorem atJoinCB_good {i : ℕ} {cur : Option Cur} {pend : Pend} {out : List Seg}
    (hcur : ∀ c, cur = some c → CurGoodCB S L fp prog entry c i)
    (hout : ∀ s ∈ out, SegGoodCB S L fp prog entry s) :
    (∀ c, (atJoin i cur pend out).1 = some c → CurGoodCB S L fp prog entry c i) ∧
      ∀ s ∈ (atJoin i cur pend out).2.2, SegGoodCB S L fp prog entry s := by
  unfold atJoin
  split
  · rename_i t a ps
    split_ifs with ht
    · cases cur with
      | some c =>
        simp only [Trie.seq_eq]
        split_ifs with hlt
        · refine ⟨fun c' hc' ↦ ?_, fun s hs ↦ ?_⟩
          · obtain rfl := Option.some.inj hc'
            exact curGoodCB_init i _
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact segGoodCB_close (hcur c rfl) [i]
            · exact hout s hs
        · refine ⟨fun c' hc' ↦ ?_, hout⟩
          obtain rfl := Option.some.inj hc'
          exact curGoodCB_init i _
      | none =>
        simp only [Trie.seq_eq]
        refine ⟨fun c' hc' ↦ ?_, hout⟩
        obtain rfl := Option.some.inj hc'
        exact curGoodCB_init i _
    · exact ⟨hcur, hout⟩
  · exact ⟨hcur, hout⟩

/-- **The walk produces segments complete with counts.** -/
private theorem passCB_good (hctx : Ctx F κ fp) : ∀ (code : List OInstr) (i : ℕ) (cur : Option Cur)
    (pend : Pend) (out : List Seg) (dead : ℕ), Fetches prog (entry + i) code →
    (∀ c, cur = some c → CurGoodCB S L fp prog entry c i) →
    (∀ s ∈ out, SegGoodCB S L fp prog entry s) →
    ∀ s ∈ (pass F entry len code i cur pend out dead).segs, SegGoodCB S L fp prog entry s
  | [], i, cur, pend, out, dead, _, hcur, hout => by
    show ∀ s ∈ (passEnd len i cur out dead).segs, _
    unfold passEnd
    cases cur with
    | none => exact hout
    | some c =>
      simp only
      by_cases hlt : c.start < i
      · rw [ite_eq_left hlt]
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact segGoodCB_close (hcur c rfl) _
        · exact hout s hs
      · rw [ite_eq_right hlt]
        exact hout
  | ins :: rest, i, cur, pend, out, dead, hf, hcur, hout => by
    show ∀ s ∈ (passStep F entry len ins (pass F entry len rest) i cur pend out dead).segs, _
    obtain ⟨hcur', hout'⟩ := atJoinCB_good (pend := pend) hcur hout
    have hrest : Fetches prog (entry + (i + 1)) rest := by
      simpa [Nat.add_assoc] using hf.tail
    obtain ⟨hfi, hpc⟩ := hf.head
    unfold passStep
    rcases hj : atJoin i cur pend out with ⟨cur', pend', out'⟩
    rw [hj] at hcur' hout'
    cases cur' with
    | none =>
      simp only [natSeq_eq]
      exact passCB_good hctx rest (i + 1) none pend' out' (dead + 1) hrest (fun _ h ↦ by cases h)
        hout'
    | some c =>
      have hc := hcur' c rfl
      simp only
      rcases hs : stepI F entry len i c.st ins with ⟨its, st⟩ | ⟨its, x⟩
      · simp only [St.seq_eq, headSeq_eq, natSeq_eq]
        exact passCB_good hctx rest (i + 1) _ _ out' dead hrest
          (fun c' h ↦ Option.some.inj h ▸ curGoodCB_go hctx hc hfi hpc hs) hout'
      · simp only [headSeq_eq, natSeq_eq]
        refine passCB_good hctx rest (i + 1) none _ _ dead hrest (fun _ h ↦ by cases h) ?_
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact segGoodCB_stop hctx hc hfi hpc hs
        · exact hout' s hs'

end Pass

/-! ## The executor, counted -/

section Main

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {f : CompiledFn}

/-- **Completeness, counted**: on a memory satisfying the atoms of a path of a segment of
`exec F f`, in a frame its environment holds of, a counted run from the segment's start reaches
the registers the path's exit names, each opcode's count at most the instructions of that opcode
among the segment's items; the path leaves by an exit of the segment (its own or a branch's)
whose kind names those registers and whose environment holds. -/
theorem execB_completeC (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) (he : EnvHolds L fp s.env) {r : Regs K}
    (h : FollowsB S L fp f.entry r (s.exit.kind.Regs L fp f.entry r) s.items) :
    ∃ c, RunCB S prog L ⟨gpow (f.entry + s.start), fp⟩ r c ∧ (∀ op, c op ≤ itemOps s.items op) ∧
      ∃ x, (x = s.exit ∨ x ∈ branchExits s.items) ∧ x.kind.Regs L fp f.entry r ∧
        EnvHolds L fp x.env :=
  passCB_good hctx f.code 0 _ [] [] 0 (by simpa using hf)
    (fun _ h ↦ Option.some.inj h ▸ curGoodCB_init 0 _) (fun _ h ↦ by cases h) s hs he r h

/-- **Completeness on a window, counted**, as `execB_completeC`. -/
theorem execWinB_completeC (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {a b : ℕ}
    {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs)
    (he : EnvHolds L fp s.env) {r : Regs K}
    (h : FollowsB S L fp f.entry r (s.exit.kind.Regs L fp f.entry r) s.items) :
    ∃ c, RunCB S prog L ⟨gpow (f.entry + s.start), fp⟩ r c ∧ (∀ op, c op ≤ itemOps s.items op) ∧
      ∃ x, (x = s.exit ∨ x ∈ branchExits s.items) ∧ x.kind.Regs L fp f.entry r ∧
        EnvHolds L fp x.env :=
  passCB_good hctx _ a _ [] [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curGoodCB_init a _) (fun _ h ↦ by cases h) s hs he r h

end Main


/-! ## At the deployed semantics -/

section Deployed

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

/-- At the deployed semantics, `runCountB` is `runCount`. -/
theorem runCountB_deployed (op : Opcode) : ∀ (n : ℕ) (r : Regs K),
    runCountB blakeDeployed prog L op n r = runCount prog L op n r
  | 0, _ => rfl
  | n + 1, r => by
    unfold runCountB runCount
    rw [stepB_deployed]
    rcases prog.fetch r.pc with _ | i <;> rcases step prog L r with _ | r' <;>
      simp only [runCountB_deployed op n]

/-- **At the deployed semantics, `RunCB` is `Count.lean`'s `RunC`.** -/
theorem runCB_deployed (s t : Regs K) (c : Opcode → ℕ) :
    RunCB blakeDeployed prog L s t c = RunC prog L s t c := by
  simp only [RunCB, RunC, runB_deployed, runCountB_deployed]

/-- At the deployed semantics, `ReachCB` is `Count.lean`'s `ReachC`. -/
theorem reachCB_deployed (s t : Regs K) (its : List Item) :
    ReachCB blakeDeployed L prog s t its = ReachC L prog s t its := by
  simp only [ReachCB, ReachC, runCB_deployed]

/-- At the deployed semantics, `LeavesCB` is `Count.lean`'s `LeavesC`. -/
theorem leavesCB_deployed (fp : K) (entry : ℕ) (s r : Regs K) (its : List Item)
    (X : Exit → Prop) :
    LeavesCB blakeDeployed L fp prog entry s r its X = LeavesC L fp prog entry s r its X := by
  simp only [LeavesCB, LeavesC, runCB_deployed]

/-- At the deployed semantics, `SegGoodCB` is `Count.lean`'s `SegGoodC`. -/
theorem segGoodCB_deployed (fp : K) (entry : ℕ) (s : Seg) :
    SegGoodCB blakeDeployed L fp prog entry s = SegGoodC L fp prog entry s := by
  simp only [SegGoodCB, SegGoodC, Exec.followsB_deployed, leavesCB_deployed]

/-- `count_eq_of_runC`'s count is the trace's (`Trace.count`) at the deployed semantics. -/
theorem runCountB_deployed_count (n : ℕ) (op : Opcode) :
    runCountB blakeDeployed prog L op n Regs.initial = (⟨κ, L, n⟩ : Trace prog).count op :=
  runCountB_deployed op n _

end Deployed

end
end LeanVM.Guest.B2C
