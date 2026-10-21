/-
  LeanVM.Guest.B2C.CplExecB

  Segments along a path (`CplExec.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplExec
public import LeanVM.Guest.B2C.CountB

/-!
# Segments along a path under any `BLAKE2S` semantics

`CplExec.lean`'s `Fall`, `Taken`, `ToC`, `ResZ`, `CurZ`, `SegZ` with `S : BlakeSem` a parameter
(`FallB`, `TakenB`, `ToCB`, `ResZB`, `CurZB`, `SegZB`), and their lemmas (`stepIB_z`,
`passZB_good`, `execWinB_z`, …), proved as there over `ExecB.lean`.

* `fallB_deployed`, `takenB_deployed`, `toCB_deployed`, `resZB_deployed`, `curZB_deployed`,
  `segZB_deployed`: at `blakeDeployed`, they are `CplExec.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

variable {S : BlakeSem}

section Defs

variable {κ : ℕ} (L : MemImage κ) (fp : K)

variable (S) in
/-- **Every item of a path holds**, every branch falling through. -/
def FallB : List Item → Prop
  | [] => True
  | .ins a :: its => a.HoldsB S L fp ∧ FallB its
  | .fact _ :: its => FallB its
  | .branch oc od of _ :: its =>
      (Atom.jump oc od of).HoldsB S L fp ∧ L.read (fp * gpow oc) = some 0 ∧ FallB its

variable (S) in
/-- **A branch is taken**: its cells hold words of `K`, its condition is not `0`. -/
def TakenB (oc od of : ℕ) : Prop :=
  (Atom.jump oc od of).HoldsB S L fp ∧ ∃ v, L.read (fp * gpow oc) = some v ∧ v ≠ 0

variable (S) in
/-- A counted run from `s` to `r` within the instructions of `its`, the exit `x`'s environment
holding. -/
def ToCB (prog : Program) (s r : Regs K) (its : List Item) (x : Exit) : Prop :=
  ∃ c, RunCB S prog L s r c ∧ (∀ op, c op ≤ itemOps its op) ∧ EnvHolds L fp x.env

end Defs

section

variable {κ : ℕ} {L : MemImage κ} {fp : K}

theorem fallB_append : ∀ (l₁ l₂ : List Item), FallB S L fp (l₁ ++ l₂) ↔ FallB S L fp l₁ ∧ FallB S L fp l₂
  | [], _ => by simp [FallB]
  | .ins a :: l₁, l₂ => by simp only [List.cons_append, FallB, fallB_append l₁ l₂, and_assoc]
  | .fact _ :: l₁, l₂ => by simp only [List.cons_append, FallB, fallB_append l₁ l₂]
  | .branch .. :: l₁, l₂ => by simp only [List.cons_append, FallB, fallB_append l₁ l₂, and_assoc]

theorem fallB_facts (fs : List Atom) : FallB S L fp (fs.map .fact) := by
  induction fs with
  | nil => trivial
  | cons a fs ih => exact ih

end

section Pass

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {entry len : ℕ}

theorem reachCB_trans {s t u : Regs K} {l₁ l₂ : List Item} (h₁ : ReachCB S L prog s t l₁)
    (h₂ : ReachCB S L prog t u l₂) : ReachCB S L prog s u (l₁ ++ l₂) := by
  obtain ⟨c₁, hc₁, hle₁⟩ := h₁
  obtain ⟨c₂, hc₂, hle₂⟩ := h₂
  refine ⟨c₁ + c₂, hc₁.trans hc₂, fun op ↦ ?_⟩
  rw [Pi.add_apply, itemOps_append]
  exact Nat.add_le_add (hle₁ op) (hle₂ op)

theorem toCB_after {s t r : Regs K} {l₁ l₂ : List Item} {x : Exit} (h₁ : ReachCB S L prog s t l₁)
    (h : ToCB S L fp prog t r l₂ x) : ToCB S L fp prog s r (l₁ ++ l₂) x := by
  obtain ⟨c₁, hc₁, hle₁⟩ := h₁
  obtain ⟨c, hc, hle, he⟩ := h
  refine ⟨c₁ + c, hc₁.trans hc, fun op ↦ ?_, he⟩
  rw [Pi.add_apply, itemOps_append]
  exact Nat.add_le_add (hle₁ op) (hle op)

variable (S) in
/-- What an instruction's result gives along a path. -/
def ResZB (L : MemImage κ) (fp : K) (prog : Program) (entry i : ℕ) : Res → Prop
  | .go its st =>
    (FallB S L fp its → St.HoldsB S L fp st ∧
      ReachCB S L prog ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩ its) ∧
    ∀ pre oc od of x post, its = pre ++ .branch oc od of x :: post → FallB S L fp pre →
      TakenB S L fp oc od of → ∀ r, x.kind.Regs L fp entry r →
        ToCB S L fp prog ⟨gpow (entry + i), fp⟩ r (pre ++ [.branch oc od of x]) x
  | .stop its x => FallB S L fp its → ∀ r, x.kind.Regs L fp entry r →
      ToCB S L fp prog ⟨gpow (entry + i), fp⟩ r its x

/-- **One instruction along a path.** -/
theorem stepIB_z (hctx : Ctx F κ fp) {i : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.HoldsB S L fp st) :
    ResZB S L fp prog entry i (stepI F entry len i st ins) := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    refine ⟨fun ⟨hh, _⟩ ↦ ?_, fun pre oc od of x post he ↦ ?_⟩
    · obtain ⟨-, he, hm⟩ := nonJumpB_holds hctx.le hctx.pows hst hh
      refine ⟨hst.push he hm hh, _, runCB_fallThrough hf hpc hj hh, fun op ↦ ?_⟩
      rw [itemOps_cons]
      exact Nat.le_add_right _ _
    · exfalso
      cases pre with
      | nil => simp at he
      | cons a pre =>
        simp only [List.cons_append, List.cons.injEq] at he
        exact branch_not_facts he.2
  | true =>
    cases ins with
    | jump oc od of =>
      have hone : ∀ (a : Item), (∀ op, itemOp a op = if op = .jump then 1 else 0) →
          ∀ op, (if op = Opcode.jump then 1 else 0) ≤ itemOps [a] op := by
        intro a ha op
        rw [itemOps_cons, itemOps_nil, ha]
        exact Nat.le_add_right _ _
      have hgo : ∀ {c d f : E} {r : Regs K}, L.read (fp * gpow oc) = some c →
          L.read (fp * gpow od) = some d → L.read (fp * gpow of) = some f → IsInK c → IsInK d →
          IsInK f → c ≠ 0 → (jumpExit F entry len i st od of).kind.Regs L fp entry r →
          RunCB S prog L ⟨gpow (entry + i), fp⟩ r (fun op ↦ if op = .jump then 1 else 0) ∧
            EnvHolds L fp (jumpExit F entry len i st od of).env := by
        intro c d f r hc hd hf' hcK hdK hfK hc0 hr
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
      · refine ⟨fun ⟨⟨c, d, f, hc, hd, hf', _, hdK, hfK⟩, _⟩ ↦ ?_, fun pre _ _ _ _ post he ↦ ?_⟩
        · have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
          obtain rfl : c = 0 := (Option.some.inj h0).symm
          exact ⟨hst, _, hnext hc hd hf' hdK hfK, hone _ fun _ ↦ rfl⟩
        · exfalso
          cases pre with
          | nil => simp at he
          | cons a pre => simp at he
      · rintro ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, -⟩ r hr
        obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        obtain ⟨hrun, he⟩ := hgo hc hd hf' hcK hdK hfK (hcw ▸ hw0) hr
        exact ⟨_, hrun, hone _ fun _ ↦ rfl, he⟩
      · refine ⟨fun ⟨⟨c, d, f, hc, hd, hf', _, hdK, hfK⟩, h0, _⟩ ↦ ?_,
          fun pre oc' od' of' x post he hpre ht r hr ↦ ?_⟩
        · obtain rfl : c = 0 := Option.some.inj (hc.symm.trans h0)
          exact ⟨hst, _, hnext hc hd hf' hdK hfK, hone _ fun _ ↦ rfl⟩
        · cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Item.branch.injEq] at he
            obtain ⟨⟨rfl, rfl, rfl, rfl⟩, -⟩ := he
            obtain ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, v, hv, hv0⟩ := ht
            obtain rfl := Option.some.inj (hv.symm.trans hc)
            obtain ⟨hrun, he⟩ := hgo hc hd hf' hcK hdK hfK hv0 hr
            exact ⟨_, hrun, hone _ fun _ ↦ rfl, he⟩
          | cons a pre =>
            exfalso
            simp only [List.cons_append, List.cons.injEq] at he
            simp at he
    | _ => simp [OInstr.isJump] at hj

variable (S) in
/-- A segment being walked, at offset `i`, along a path. -/
def CurZB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (c : Cur) (i : ℕ) : Prop :=
  EnvHolds L fp c.env →
    (FallB S L fp c.acc.reverse → St.HoldsB S L fp c.st ∧
      ReachCB S L prog ⟨gpow (entry + c.start), fp⟩ ⟨gpow (entry + i), fp⟩ c.acc.reverse) ∧
    ∀ pre oc od of x post, c.acc.reverse = pre ++ .branch oc od of x :: post → FallB S L fp pre →
      TakenB S L fp oc od of → ∀ r, x.kind.Regs L fp entry r →
        ToCB S L fp prog ⟨gpow (entry + c.start), fp⟩ r (pre ++ [.branch oc od of x]) x

variable (S) in
/-- **A segment along a path**: all its items holding, it reaches its exit's registers; leaving
by a taken branch, that branch's, each with that exit's environment holding. -/
def SegZB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (s : Seg) : Prop :=
  EnvHolds L fp s.env →
    (FallB S L fp s.items → ∀ r, s.exit.kind.Regs L fp entry r →
      ToCB S L fp prog ⟨gpow (entry + s.start), fp⟩ r s.items s.exit) ∧
    ∀ pre oc od of x post, s.items = pre ++ .branch oc od of x :: post → FallB S L fp pre →
      TakenB S L fp oc od of → ∀ r, x.kind.Regs L fp entry r →
        ToCB S L fp prog ⟨gpow (entry + s.start), fp⟩ r (pre ++ [.branch oc od of x]) x

theorem curZB_init (i : ℕ) (env : Trie Sym) : CurZB S L fp prog entry (Cur.init i env) i := by
  intro he
  refine ⟨fun _ ↦ ⟨stHoldsB_init he, 0, RunCB.refl _, fun _ ↦ Nat.zero_le _⟩,
    fun pre _ _ _ _ post h ↦ ?_⟩
  simp [Cur.init] at h

theorem segZB_close {c : Cur} {i : ℕ} (hc : CurZB S L fp prog entry c i) (succ : List ℕ) :
    SegZB S L fp prog entry (c.close [] ⟨.next i, c.st.env, succ⟩) := by
  intro he
  have hc := hc he
  simp only [Cur.close, items_close, List.append_nil]
  refine ⟨fun hf r hr ↦ ?_, hc.2⟩
  obtain ⟨hst, n, hn, hle⟩ := hc.1 hf
  simp only [Kind.Regs] at hr
  subst hr
  exact ⟨n, hn, hle, hst.1⟩

theorem curZB_go (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurZB S L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {st : St}
    (hs : stepI F entry len i c.st ins = .go its st) :
    CurZB S L fp prog entry
      ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩ (i + 1) := by
  intro he
  have hc := hc he
  simp only [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]
  refine ⟨fun hfall ↦ ?_, fun pre oc od of x post hsp hpre ht r hr ↦ ?_⟩
  · obtain ⟨hA, hB⟩ := (fallB_append _ _).mp hfall
    obtain ⟨hst, h⟩ := hc.1 hA
    have := stepIB_z (len := len) hctx hf hpc hst
    rw [hs] at this
    obtain ⟨hst', h'⟩ := this.1 hB
    refine ⟨hst', ?_⟩
    have e : entry + i + 1 = entry + (i + 1) := by omega
    rw [e] at h'
    exact reachCB_trans h h'
  · rcases split_branch hsp with ⟨post', hA⟩ | ⟨pre', rfl, hB⟩
    · exact hc.2 pre oc od of x post' hA hpre ht r hr
    · obtain ⟨hA, hpre'⟩ := (fallB_append _ _).mp hpre
      obtain ⟨hst, h⟩ := hc.1 hA
      have := stepIB_z (len := len) hctx hf hpc hst
      rw [hs] at this
      have h' := this.2 pre' oc od of x post hB hpre' ht r hr
      rw [List.append_assoc]
      exact toCB_after h h'

theorem segZB_stop (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurZB S L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {x : Exit}
    (hs : stepI F entry len i c.st ins = .stop its x) : SegZB S L fp prog entry (c.close its x) := by
  intro he
  have hc := hc he
  have hits : ∃ oc od of, its = [.ins (.jump oc od of)] := by
    cases ins with
    | jump oc od of =>
      simp only [stepI, optSeq_eq] at hs
      split_ifs at hs
      cases hs
      exact ⟨_, _, _, rfl⟩
    | _ => rw [stepI_of_nonJump rfl] at hs; cases hs
  simp only [Cur.close, items_close]
  refine ⟨fun hfall r hr ↦ ?_, fun pre oc od of x' post hsp hpre ht r hr ↦ ?_⟩
  · obtain ⟨hA, hB⟩ := (fallB_append _ _).mp hfall
    obtain ⟨hst, h⟩ := hc.1 hA
    have := stepIB_z (len := len) hctx hf hpc hst
    rw [hs] at this
    exact toCB_after h (this hB r hr)
  · rcases split_branch hsp with ⟨post', hA⟩ | ⟨pre', rfl, hB⟩
    · exact hc.2 pre oc od of x' post' hA hpre ht r hr
    · exfalso
      obtain ⟨_, _, _, h⟩ := hits
      rw [h] at hB
      cases pre' with
      | nil => simp at hB
      | cons a pre' => simp at hB

theorem atJoinZB_good {i : ℕ} {cur : Option Cur} {pend : Pend} {out : List Seg}
    (hcur : ∀ c, cur = some c → CurZB S L fp prog entry c i)
    (hout : ∀ s ∈ out, SegZB S L fp prog entry s) :
    (∀ c, (atJoin i cur pend out).1 = some c → CurZB S L fp prog entry c i) ∧
      ∀ s ∈ (atJoin i cur pend out).2.2, SegZB S L fp prog entry s := by
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
            exact curZB_init i _
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact segZB_close (hcur c rfl) [i]
            · exact hout s hs
        · refine ⟨fun c' hc' ↦ ?_, hout⟩
          obtain rfl := Option.some.inj hc'
          exact curZB_init i _
      | none =>
        simp only [Trie.seq_eq]
        refine ⟨fun c' hc' ↦ ?_, hout⟩
        obtain rfl := Option.some.inj hc'
        exact curZB_init i _
    · exact ⟨hcur, hout⟩
  · exact ⟨hcur, hout⟩

/-- **The walk produces segments complete along every path.** -/
theorem passZB_good (hctx : Ctx F κ fp) : ∀ (code : List OInstr) (i : ℕ) (cur : Option Cur)
    (pend : Pend) (out : List Seg) (dead : ℕ), Fetches prog (entry + i) code →
    (∀ c, cur = some c → CurZB S L fp prog entry c i) →
    (∀ s ∈ out, SegZB S L fp prog entry s) →
    ∀ s ∈ (pass F entry len code i cur pend out dead).segs, SegZB S L fp prog entry s
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
        · exact segZB_close (hcur c rfl) _
        · exact hout s hs
      · rw [ite_eq_right hlt]
        exact hout
  | ins :: rest, i, cur, pend, out, dead, hf, hcur, hout => by
    show ∀ s ∈ (passStep F entry len ins (pass F entry len rest) i cur pend out dead).segs, _
    obtain ⟨hcur', hout'⟩ := atJoinZB_good (pend := pend) hcur hout
    have hrest : Fetches prog (entry + (i + 1)) rest := by
      simpa [Nat.add_assoc] using hf.tail
    obtain ⟨hfi, hpc⟩ := hf.head
    unfold passStep
    rcases hj : atJoin i cur pend out with ⟨cur', pend', out'⟩
    rw [hj] at hcur' hout'
    cases cur' with
    | none =>
      simp only [natSeq_eq]
      exact passZB_good hctx rest (i + 1) none pend' out' (dead + 1) hrest (fun _ h ↦ by cases h)
        hout'
    | some c =>
      have hc := hcur' c rfl
      simp only
      rcases hs : stepI F entry len i c.st ins with ⟨its, st⟩ | ⟨its, x⟩
      · simp only [St.seq_eq, headSeq_eq, natSeq_eq]
        exact passZB_good hctx rest (i + 1) _ _ out' dead hrest
          (fun c' h ↦ Option.some.inj h ▸ curZB_go hctx hc hfi hpc hs) hout'
      · simp only [headSeq_eq, natSeq_eq]
        refine passZB_good hctx rest (i + 1) none _ _ dead hrest (fun _ h ↦ by cases h) ?_
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact segZB_stop hctx hc hfi hpc hs
        · exact hout' s hs'

/-- **Every segment of a window is complete along every path.** -/
theorem execWinB_z (hctx : Ctx F κ fp) {f : CompiledFn} (hf : Fetches prog f.entry f.code)
    {a b : ℕ} {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs) :
    SegZB S L fp prog f.entry s :=
  passZB_good hctx _ a _ [] [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curZB_init a _) (fun _ h ↦ by cases h) s hs

end Pass


/-! ## At the deployed semantics -/

section Deployed

variable {κ : ℕ} {L : MemImage κ} {fp : K}

/-- At the deployed semantics, `FallB` is `CplExec.lean`'s `Fall`. -/
theorem fallB_deployed : ∀ its : List Item, FallB blakeDeployed L fp its = Fall L fp its
  | [] => rfl
  | .ins a :: its => by simp only [FallB, Fall, Exec.atom_holdsB_deployed, fallB_deployed its]
  | .fact _ :: its => by simp only [FallB, Fall, fallB_deployed its]
  | .branch oc od of x :: its => by
    simp only [FallB, Fall, Exec.atom_holdsB_deployed, fallB_deployed its]

/-- At the deployed semantics, `TakenB` is `CplExec.lean`'s `Taken`. -/
theorem takenB_deployed (oc od of : ℕ) : TakenB blakeDeployed L fp oc od of = Taken L fp oc od of :=
  rfl

/-- At the deployed semantics, `ToCB` is `CplExec.lean`'s `ToC`. -/
theorem toCB_deployed (prog : Program) (s r : Regs K) (its : List Item) (x : Exit) :
    ToCB blakeDeployed L fp prog s r its x = ToC L fp prog s r its x := by
  simp only [ToCB, ToC, runCB_deployed]

/-- At the deployed semantics, `ResZB` is `CplExec.lean`'s `ResZ`. -/
theorem resZB_deployed (prog : Program) (entry i : ℕ) (res : Res) :
    ResZB blakeDeployed L fp prog entry i res = ResZ L fp prog entry i res := by
  cases res <;> simp only [ResZB, ResZ, fallB_deployed, takenB_deployed, toCB_deployed,
    Exec.st_holdsB_deployed, reachCB_deployed]

/-- At the deployed semantics, `CurZB` is `CplExec.lean`'s `CurZ`. -/
theorem curZB_deployed (prog : Program) (entry : ℕ) (c : Cur) (i : ℕ) :
    CurZB blakeDeployed L fp prog entry c i = CurZ L fp prog entry c i := by
  simp only [CurZB, CurZ, fallB_deployed, takenB_deployed, toCB_deployed,
    Exec.st_holdsB_deployed, reachCB_deployed]

/-- At the deployed semantics, `SegZB` is `CplExec.lean`'s `SegZ`. -/
theorem segZB_deployed (prog : Program) (entry : ℕ) (s : Seg) :
    SegZB blakeDeployed L fp prog entry s = SegZ L fp prog entry s := by
  simp only [SegZB, SegZ, fallB_deployed, takenB_deployed, toCB_deployed]

end Deployed

end
end LeanVM.Guest.B2C
