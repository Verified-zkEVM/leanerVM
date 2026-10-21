/-
  LeanVM.Guest.ExecB

  The symbolic executor's soundness and completeness (`Exec.lean`) under any semantics of
  `BLAKE2S`: the executor itself is `Exec.lean`'s, its semantics over `LogicB`.
-/

module

public import LeanVM.Guest.Exec
public import LeanVM.Guest.LogicB

/-!
# The symbolic executor under any `BLAKE2S` semantics

`Exec.lean`'s executor walks code, not semantics: an atom it records for a non-`JUMP`
instruction is the instruction (`Atom.instr`), and its facts (`nonJump`) never read a
`BLAKE2S` row. So its soundness and completeness hold over any `S : BlakeSem` as they do over the
deployed one; here they are, each definition and lemma of `Exec.lean` that mentions the program
logic renamed with a `B` (`St.HoldsB`, `Atom.HoldsB`, `RunKB`, `FollowsB`, `execB_sound`,
`execB_complete`, `execWinB_sound`, …) and proved as there. What does not mention it (the
executor, the environments `EnvHolds`, `MemHolds`) is `Exec.lean`'s.
-/

namespace LeanVM.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

variable {S : BlakeSem}

/-! ## Evaluation order

The kernel evaluates by substitution and does not share the evaluation of a term between its
copies, so a value that a walk inspects at every step is passed on evaluated: each `seq`
evaluates its argument to a constructor and hands that on, and the functions that build the
walk's state build it evaluated. Each `seq` is the identity (`seq_eq`). -/

section

variable {α β : Type}

end

/-! ## Tries keyed by `ℕ` -/

namespace Trie

variable {α β : Type}

/-! Written with the recursors, which the kernel reduces much faster than the compiled form of
structural recursion; hence `noncomputable`: these are evaluated by the kernel only. -/

end Trie

/-! ## Symbolic values -/

/-! ## Facts from outside -/

/-! ## Atoms, items, exits, segments -/

/-! ## One instruction -/

/-! ## The pass -/

/-! ## Linking -/

/-! ## Tries: lemmas -/

namespace Trie

variable {α : Type}

end Trie

/-! ## Semantics -/

section Semantics

variable {κ : ℕ} (L : MemImage κ) (fp : K)

variable (S) in
/-- What is known along a path holds. -/
def St.HoldsB (st : St) : Prop :=
  EnvHolds L fp st.env ∧ MemHolds L fp st.mem ∧ ∀ x ∈ st.prev, Guest.HoldsB S L x.1 fp x.2

variable (S) in
/-- **What an atom means**, of the memory and the frame. -/
def Atom.HoldsB : Atom → Prop
  | .instr pc ins => Guest.HoldsB S L pc fp ins
  | .jump oc od of => ∃ c d f, L.read (fp * gpow oc) = some c ∧ L.read (fp * gpow od) = some d ∧
      L.read (fp * gpow of) = some f ∧ IsInK c ∧ IsInK d ∧ IsInK f
  | .copy dst src => ∃ v, L.read (fp * gpow src) = some v ∧ L.read (fp * gpow dst) = some v
  | .eq a b => ∃ v, L.read (fp * gpow a) = some v ∧ L.read (fp * gpow b) = some v
  | .nz x => ∃ v, L.read (fp * gpow x) = some v ∧ v ≠ 0
  | .ne a b => ∃ u v, L.read (fp * gpow a) = some u ∧ L.read (fp * gpow b) = some v ∧ u ≠ v
  | .bool x => ∃ v, L.read (fp * gpow x) = some v ∧ (v = 0 ∨ v = 1)
  | .range x y k => ∃ e e', e + e' + 1 = k ∧ L.read (fp * gpow x) = some (ofK (gpow e)) ∧
      L.read (fp * gpow y) = some (ofK (gpow e'))
  | .powPair x y z => ∃ e e', e < 2 ^ κ ∧ e' < 2 ^ κ ∧
      L.read (fp * gpow x) = some (ofK (gpow e)) ∧ L.read (fp * gpow y) = some (ofK (gpow e')) ∧
      L.read (fp * gpow z) = some (ofK (gpow (e + e')))

variable (S) in
/-- **Completeness along a path**: the atoms of `its` hold until the path leaves by a branch
whose exit goes to `r`, or reaches its end with `Q`. -/
def FollowsB (entry : ℕ) (r : Regs K) (Q : Prop) : List Item → Prop
  | [] => Q
  | .ins a :: its => a.HoldsB S L fp ∧ FollowsB entry r Q its
  | .fact _ :: its => FollowsB entry r Q its
  | .branch oc od of x :: its => (Atom.jump oc od of).HoldsB S L fp ∧
      ((L.read (fp * gpow oc) = some 0 ∧ FollowsB entry r Q its) ∨
        ((∃ v, L.read (fp * gpow oc) = some v ∧ v ≠ 0) ∧ x.kind.Regs L fp entry r))

variable (prog : Program)

variable (S) in
/-- An exit is reached with `k` steps left, fewer than the `k₀` the path started with: its
environment and extra facts hold, and the run goes on from its registers. -/
def Exit.ReachedB (entry k₀ : ℕ) (x : Exit) (k : ℕ) : Prop :=
  k < k₀ ∧ EnvHolds L fp x.env ∧ x.kind.Extra L fp ∧
    ∃ r, x.kind.Regs L fp entry r ∧ SafeB S prog L k r

variable (S) in
/-- **Soundness along a path**: from `k` steps left, every atom of `its` holds on the path the run
takes, each executed instruction a step, and the run leaves by a branch's exit, or reaches the
end with `Q` of the steps left. -/
def RunKB (entry k₀ : ℕ) (Q : ℕ → Prop) : List Item → ℕ → Prop
  | [], k => Q k
  | .ins a :: its, k => a.HoldsB S L fp ∧ ∃ k', k = k' + 1 ∧ RunKB entry k₀ Q its k'
  | .fact a :: its, k => a.HoldsB S L fp ∧ RunKB entry k₀ Q its k
  | .branch oc od of x :: its, k => (Atom.jump oc od of).HoldsB S L fp ∧ ∃ k', k = k' + 1 ∧
      ((L.read (fp * gpow oc) = some 0 ∧ RunKB entry k₀ Q its k') ∨
        ((∃ v, L.read (fp * gpow oc) = some v ∧ v ≠ 0) ∧ x.ReachedB S L fp prog entry k₀ k'))

end Semantics

/-! ## Lemmas on values -/

section Values

end Values

section Env

variable {κ : ℕ} {L : MemImage κ} {fp : K}

end Env

/-! ## One instruction: soundness and completeness -/

section Step

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts}

theorem mulFactsB_holds {a b c pc : ℕ} {env : Trie Sym} (he : EnvHolds L fp env)
    (hh : Guest.HoldsB S L pc fp (.mul a b c)) :
    ∀ x ∈ mulFacts a b c (env.get a) (env.get b), x.HoldsB S L fp := by
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  intro x hx
  simp only [mulFacts, List.mem_append] at hx
  rcases hx with hx | hx
  · split_ifs at hx with hab
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [List.mem_singleton] at hx
      subst hx
      obtain rfl := Option.some.inj (hA.symm.trans hB)
      have hsq := Option.some.inj (hA.symm.trans hC)
      refine ⟨_, hA, ?_⟩
      by_cases h0 : vA = 0
      · exact Or.inl h0
      · exact Or.inr (mul_left_cancel₀ h0 ((mul_one vA).trans hsq)).symm
    · simp at hx
  · split_ifs at hx with h1 h2
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨w, hw, hw1⟩ := isOne_val h1 fp
      have := (he b w hw).symm.trans hB
      rw [hw1] at this
      obtain rfl := Option.some.inj this
      exact ⟨vA, hA, by rw [hC, mul_one]⟩
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨w, hw, hw1⟩ := isOne_val h2 fp
      have := (he a w hw).symm.trans hA
      rw [hw1] at this
      obtain rfl := Option.some.inj this
      exact ⟨vB, hB, by rw [hC, one_mul]⟩
    · simp at hx

theorem mulEnvB_holds {a b c pc : ℕ} {env : Trie Sym} (he : EnvHolds L fp env)
    (hh : Guest.HoldsB S L pc fp (.mul a b c)) : EnvHolds L fp (mulEnv F env a b c) := by
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  unfold mulEnv
  cases F.scaled.contains a
  · exact he
  · simp only [Bool.cond_true]
    split
    · rename_i e hea
      split
      · rename_i e' heb
        apply he.learn
        obtain ⟨w, hw, hwv⟩ := expo_val heb fp
        obtain rfl := Option.some.inj ((he a _ hea).symm.trans hA)
        obtain rfl := Option.some.inj ((he b w hw).symm.trans hB)
        rw [hC, hwv, Sym.val, Sym.val, ← ofK_mul, mul_assoc, gpow, gpow, gpow, pow_add]
      · exact he
    · exact he

theorem neFactsB_holds {o pc : ℕ} {prev : List (ℕ × OInstr)}
    (hprev : ∀ x ∈ prev, Guest.HoldsB S L x.1 fp x.2) (hh : Guest.HoldsB S L pc fp (.set o 1 0 0)) :
    ∀ x ∈ neFacts o prev, x.HoldsB S L fp := by
  have h1 : L.read (fp * gpow o) = some 1 := by
    rw [show (1 : E) = OInstr.imm 1 0 0 from (imm_of_ofBits rfl).trans ofK_one |>.symm]
    exact hh
  unfold neFacts
  split
  next _ x y p' rest =>
    split_ifs with hp
    · subst hp
      obtain ⟨vX, vY, hX, hY, hP⟩ := hprev _ List.mem_cons_self
      have hxy : vX * vY = 1 := Option.some.inj (hP.symm.trans h1)
      have hx0 : vX ≠ 0 := fun h0 ↦ by simp [h0] at hxy
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨vX, hX, hx0⟩
      · split at hz
        next _ a b x' =>
          split_ifs at hz with hx'
          · simp only [List.mem_singleton] at hz
            subst hz hx'
            obtain ⟨vA, vB, hA, hB, hX'⟩ := hprev _ (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain rfl := Option.some.inj (hX.symm.trans hX')
            refine ⟨vA, vB, hA, hB, fun hab ↦ hx0 ?_⟩
            rw [hab, CharTwo.add_self_eq_zero]
          · simp at hz
        next => simp at hz
    · intro z hz
      simp at hz
  next =>
    intro z hz
    simp at hz

theorem rangeFactB_holds (hκ : κ ≤ 32) {y t pc : ℕ} {env : Trie Sym} {prev : List (ℕ × OInstr)}
    (he : EnvHolds L fp env) (hprev : ∀ x ∈ prev, Guest.HoldsB S L x.1 fp x.2)
    (hh : Guest.HoldsB S L pc fp (.deref y 0 t .cell)) : ∀ a ∈ rangeFact env y prev, a.HoldsB S L fp := by
  unfold rangeFact
  split
  next _ x y' z _ x' _ =>
    split_ifs with hxy
    · obtain ⟨rfl, rfl⟩ := hxy
      obtain ⟨vX, vY, hX, hY, hZ⟩ := hprev _ List.mem_cons_self
      obtain ⟨p, v3, hp, hpK, -, hp0⟩ := hprev _ (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨q, w3, hq, hqK, -, hq0⟩ := hh
      obtain ⟨i, hi, rfl⟩ := deref0_addr hκ hpK hp0
      obtain ⟨j, hj, rfl⟩ := deref0_addr hκ hqK hq0
      obtain rfl := Option.some.inj (hX.symm.trans hp)
      obtain rfl := Option.some.inj (hY.symm.trans hq)
      rw [ofK_gpow_mul] at hZ
      split
      · rename_i k hk
        split_ifs with hk63
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          obtain ⟨w, hw, hwv⟩ := expo_val hk fp
          have := (he z w hw).symm.trans hZ
          rw [hwv] at this
          have hij := gpow_injOn (show k ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega)
            (show i + j ∈ Set.Iio (2 ^ 64 - 1) by
              have : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
              simp only [Set.mem_Iio]; omega)
            (ofK_injective (Option.some.inj this))
          exact ⟨i, j, by omega, hp, hq⟩
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          exact ⟨i, j, hi, hj, hp, hq, hZ⟩
      · intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨i, j, hi, hj, hp, hq, hZ⟩
    · intro a ha
      simp at ha
  next =>
    intro a ha
    simp at ha

theorem derefMemB_holds {pc o1 o2 o3 : ℕ} {mode : DerefMode} {st : St} (hst : St.HoldsB S L fp st)
    (hh : Guest.HoldsB S L pc fp (.deref o1 o2 o3 mode)) :
    EnvHolds L fp (derefMem pc st o1 o2 o3 mode).1 ∧
      MemHolds L fp (derefMem pc st o1 o2 o3 mode).2 := by
  obtain ⟨p, v3, hp, hpK, h3, hs⟩ := hh
  cases mode with
  | fp =>
    refine ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, ?_⟩).take 4⟩
    rw [hs, derefSource_fp, Sym.val, gpow_zero', mul_one]
  | pc =>
    refine ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, ?_⟩).take 4⟩
    rw [hs, derefSource_pc]
    rfl
  | cell =>
    simp only [derefMem]
    split
    · rename_i v hv
      obtain ⟨p', hp', -, hs'⟩ := hst.2.1 _ _ _ (memFind_mem hv)
      obtain rfl := Option.some.inj (hp.symm.trans hp')
      have : v3 = v.val fp := Option.some.inj (hs.symm.trans hs')
      exact ⟨hst.1.learn (this ▸ h3), hst.2.1⟩
    · cases o2 == 0
      · exact ⟨hst.1, hst.2.1⟩
      · simp only [Bool.cond_true]
        split
        · rename_i v hv
          have : v3 = v.val fp := Option.some.inj (h3.symm.trans (hst.1 _ _ hv))
          exact ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, this ▸ hs⟩).take 4⟩
        · exact ⟨hst.1, hst.2.1⟩

/-- **A non-`JUMP` teaches only what holds.** -/
theorem nonJumpB_holds (hκ : κ ≤ 32) (hp : F.pows.Ok) {pc : ℕ} {st : St} {ins : OInstr}
    (hst : St.HoldsB S L fp st) (hh : Guest.HoldsB S L pc fp ins) :
    (∀ a ∈ (nonJump F pc st ins).1, a.HoldsB S L fp) ∧ EnvHolds L fp (nonJump F pc st ins).2.1 ∧
      MemHolds L fp (nonJump F pc st ins).2.2 := by
  cases ins with
  | xor a b c =>
    refine ⟨?_, hst.1, hst.2.1⟩
    simp only [nonJump]
    split_ifs with hz
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨vA, vB, hA, hB, hC⟩ := hh
      have := (hst.1 c _ (isZero_eq hz)).symm.trans hC
      exact ⟨vA, hA, by rw [hB, eq_of_add_eq_zero (Option.some.inj this).symm]⟩
    · intro x hx
      simp at hx
  | mul a b c => exact ⟨mulFactsB_holds hst.1 hh, mulEnvB_holds hst.1 hh, hst.2.1⟩
  | set o k0 k1 k2 =>
    refine ⟨?_, ?_, hst.2.1⟩
    · simp only [nonJump]
      split_ifs with hk
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        exact neFactsB_holds hst.2.2 hh
      · intro x hx
        simp at hx
    · simp only [nonJump]
      split
      · rename_i v hv
        exact hst.1.set (by rw [← symOf_val hp hv fp]; exact hh)
      · exact hst.1
  | deref o1 o2 o3 mode =>
    refine ⟨?_, derefMemB_holds hst hh⟩
    simp only [nonJump]
    split_ifs with hm
    · obtain ⟨rfl, rfl⟩ := hm
      exact rangeFactB_holds hκ hst.1 hst.2.2 hh
    · intro x hx
      simp at hx
  | blake2s => exact ⟨fun x hx ↦ by simp [nonJump] at hx, hst.1, hst.2.1⟩
  | jump => exact absurd hh id

theorem St.HoldsB.push {st : St} (hst : St.HoldsB S L fp st) {env : Trie Sym}
    {mem : List (ℕ × ℕ × Sym)} (he : EnvHolds L fp env) (hm : MemHolds L fp mem) {pc : ℕ}
    {ins : OInstr} (hh : Guest.HoldsB S L pc fp ins) : St.HoldsB S L fp (st.push env mem pc ins) := by
  refine ⟨he, hm, fun x hx ↦ ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hh
  · exact hst.2.2 x (List.mem_of_mem_take hx)

/-- **Where a `JUMP` goes is what its exit says.** -/
theorem jumpKindB_holds (hfp : F.fpOne = true → fp = 1) {entry len i od of : ℕ} {st : St}
    (hst : St.HoldsB S L fp st) {d f : E} (hd : L.read (fp * gpow od) = some d) (hdK : IsInK d)
    (hf : L.read (fp * gpow of) = some f) (hfK : IsInK f) :
    (jumpKind F entry len i st od of).1.Regs L fp entry ⟨d.limb 0, f.limb 0⟩ ∧
      (jumpKind F entry len i st od of).1.Extra L fp := by
  unfold jumpKind
  split_ifs with h01
  · obtain ⟨rfl, rfl⟩ := h01
    exact ⟨retRegs_eq_some_iff.mpr ⟨d, f, hd, hf, rfl⟩, trivial⟩
  · rw [Tgt.seq_eq, Tgt.seq_eq]
    have hpt := tgtOf_is hst.1 hd hdK
    have hft := tgtOf_is hst.1 hf hfK
    generalize tgtOf (st.env.get od) od = pt at hpt
    generalize hg : tgtOf (st.env.get of) of = ft at hft
    split_ifs with hself
    · have hb := self_is hfp hself hft
      split
      · rename_i e
        split_ifs with hl
        · refine ⟨?_, trivial⟩
          simp only [Kind.Regs, Tgt.Is] at hpt ⊢
          rw [hpt, hb, show entry + (e - entry) = e by omega]
        · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
    · split
      · rename_i q
        obtain rfl := tgtOf_cell hg
        split
        · rename_i r v0 h0 h1
          obtain ⟨w, hw, hwv⟩ := expo_val h0 fp
          obtain ⟨p, hp, hpK, hp0⟩ := hst.2.1 _ _ _ (memFind_mem hw)
          obtain ⟨p', hp', -, hp1⟩ := hst.2.1 _ _ _ (memFind_mem h1)
          obtain rfl := Option.some.inj (hp.symm.trans hp')
          obtain rfl := Option.some.inj (hp.symm.trans hf)
          refine ⟨⟨_, _, hp, hpK, hpt, rfl⟩, p, hp, ?_⟩
          rw [hwv] at hp0
          rw [Sym.val, gpow_zero', mul_one] at hp1
          exact retRegs_eq_some_iff.mpr ⟨_, _, hp0, hp1, by simp⟩
        · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩

end Step

/-! ## One instruction against the run -/

section StepRun

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program}

variable (S) in
/-- What an instruction's result says of the run from it, with `k` steps left: on to the next
offset with one step fewer, or out by an exit. -/
def Res.SoundB (L : MemImage κ) (fp : K) (prog : Program) (entry k₀ i k : ℕ) : Res → Prop
  | .go its st => RunKB S L fp prog entry k₀
      (fun k' ↦ k' + 1 = k ∧ St.HoldsB S L fp st ∧ SafeB S prog L k' ⟨gpow (entry + i + 1), fp⟩) its k
  | .stop its x => RunKB S L fp prog entry k₀ (x.ReachedB S L fp prog entry k₀) its k

variable (S) in
/-- What an instruction's result gives a run to `r`: from its atoms, the run reaches `r` by an
exit, or the next offset with `Q`. -/
def Res.CompB (L : MemImage κ) (fp : K) (prog : Program) (entry i : ℕ) (r : Semantics.Regs K) :
    Res → Prop
  | .go its st => ∀ Q : Prop, FollowsB S L fp entry r Q its →
      ReachB S prog L ⟨gpow (entry + i), fp⟩ r ∨
        (Q ∧ St.HoldsB S L fp st ∧ ReachB S prog L ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩)
  | .stop its x => FollowsB S L fp entry r (x.kind.Regs L fp entry r) its →
      ReachB S prog L ⟨gpow (entry + i), fp⟩ r

theorem runKB_facts {entry k₀ k : ℕ} {Q : ℕ → Prop} {fs : List Atom}
    (h : ∀ a ∈ fs, a.HoldsB S L fp) (hq : Q k) : RunKB S L fp prog entry k₀ Q (fs.map .fact) k := by
  induction fs with
  | nil => exact hq
  | cons a fs ih =>
    exact ⟨h a List.mem_cons_self, ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

theorem followsB_facts {entry : ℕ} {r : Semantics.Regs K} {Q : Prop} {fs : List Atom} :
    FollowsB S L fp entry r Q (fs.map .fact) ↔ Q := by
  induction fs with
  | nil => rfl
  | cons a fs ih => exact ih

theorem jumpB_atom {oc od of : ℕ} {c d f : E} (hc : L.read (fp * gpow oc) = some c)
    (hd : L.read (fp * gpow od) = some d) (hf : L.read (fp * gpow of) = some f) (hcK : IsInK c)
    (hdK : IsInK d) (hfK : IsInK f) : (Atom.jump oc od of).HoldsB S L fp :=
  ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK⟩

/-- **One instruction is sound.** -/
theorem stepIB_sound (hctx : Ctx F κ fp) {entry len i k k₀ : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.HoldsB S L fp st) (hk : k ≤ k₀)
    (h : SafeB S prog L k ⟨gpow (entry + i), fp⟩) :
    (stepI F entry len i st ins).SoundB S L fp prog entry k₀ i k := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    obtain ⟨k', rfl, hh, hs⟩ := h.fallThrough hf hpc hj
    obtain ⟨hfs, he, hm⟩ := nonJumpB_holds hctx.le hctx.pows hst hh
    exact ⟨hh, k', rfl, runKB_facts hfs ⟨rfl, hst.push he hm hh, hs⟩⟩
  | true =>
    cases ins with
    | jump oc od of =>
      obtain ⟨k', r, rfl, ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, rfl⟩, hs⟩ := h.jump hf hpc
      have hatom := jumpB_atom (S := S) hc hd hf' hcK hdK hfK
      obtain ⟨hreg, hext⟩ := jumpKindB_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst hd
        hdK hf' hfK
      have hreach : ∀ x, x = jumpExit F entry len i st od of → c ≠ 0 →
          x.ReachedB S L fp prog entry k₀ k' := by
        rintro x rfl hc0
        rw [ite_eq_right hc0] at hs
        exact ⟨by omega, hst.1, hext, _, hreg, hs⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        rw [ite_eq_left rfl] at hs
        exact ⟨hatom, k', rfl, rfl, hst, by simpa [Nat.add_assoc] using hs⟩
      · obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        exact ⟨hatom, k', rfl, hreach _ rfl (hcw ▸ hw0)⟩
      · refine ⟨hatom, k', rfl, ?_⟩
        by_cases hc0 : c = 0
        · subst hc0
          rw [ite_eq_left rfl] at hs
          exact Or.inl ⟨hc, rfl, hst, by simpa [Nat.add_assoc] using hs⟩
        · exact Or.inr ⟨⟨c, hc, hc0⟩, hreach _ rfl hc0⟩
    | _ => simp [OInstr.isJump] at hj

/-- **One instruction is complete.** -/
theorem stepIB_complete (hctx : Ctx F κ fp) {entry len i : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.HoldsB S L fp st) (r : Semantics.Regs K) :
    (stepI F entry len i st ins).CompB S L fp prog entry i r := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    rintro Q ⟨hh, hq⟩
    rw [followsB_facts] at hq
    obtain ⟨-, he, hm⟩ := nonJumpB_holds hctx.le hctx.pows hst hh
    exact Or.inr ⟨hq, hst.push he hm hh, reachB_fallThrough hf hpc hj hh⟩
  | true =>
    cases ins with
    | jump oc od of =>
      have hgo : ∀ {c d f : E}, L.read (fp * gpow oc) = some c → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK c → IsInK d → IsInK f → c ≠ 0 →
          (jumpExit F entry len i st od of).kind.Regs L fp entry r →
          ReachB S prog L ⟨gpow (entry + i), fp⟩ r := by
        intro c d f hc hd hf' hcK hdK hfK hc0 hr
        obtain ⟨hreg, -⟩ := jumpKindB_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst
          hd hdK hf' hfK
        rw [jumpExit_eq] at hr
        obtain rfl := Kind.regs_unique hr hreg
        exact reachB_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩
      have hnext : ∀ {d f : E}, L.read (fp * gpow oc) = some 0 → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK d → IsInK f →
          ReachB S prog L ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩ := by
        intro d f hc hd hf' hdK hfK
        exact reachB_jump hf hpc ⟨0, d, f, hc, hd, hf', (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩, hdK,
          hfK, by rw [ite_eq_left rfl]⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', -, hdK, hfK⟩, hq⟩
        have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        exact Or.inr ⟨hq, hst, hnext hc hd hf' hdK hfK⟩
      · rintro ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, hr⟩
        obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        exact hgo hc hd hf' hcK hdK hfK (hcw ▸ hw0) hr
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, ⟨h0, hq⟩ | ⟨⟨v, hv, hv0⟩, hr⟩⟩
        · obtain rfl : c = 0 := Option.some.inj (hc.symm.trans h0)
          exact Or.inr ⟨hq, hst, hnext hc hd hf' hdK hfK⟩
        · obtain rfl := Option.some.inj (hv.symm.trans hc)
          exact Or.inl (hgo hc hd hf' hcK hdK hfK hv0 hr)
    | _ => simp [OInstr.isJump] at hj

end StepRun

/-! ## Paths: composition -/

section Paths

variable {κ : ℕ} {L : MemImage κ} {fp : K} {prog : Program}

theorem RunKB.mono {entry k₀ : ℕ} {Q Q' : ℕ → Prop} (hQ : ∀ k, Q k → Q' k) :
    ∀ {its : List Item} {k : ℕ}, RunKB S L fp prog entry k₀ Q its k →
      RunKB S L fp prog entry k₀ Q' its k
  | [], _, h => hQ _ h
  | .ins _ :: _, _, ⟨ha, k', hk, h⟩ => ⟨ha, k', hk, RunKB.mono hQ h⟩
  | .fact _ :: _, _, ⟨ha, h⟩ => ⟨ha, RunKB.mono hQ h⟩
  | .branch _ _ _ _ :: _, _, ⟨ha, k', hk, h⟩ =>
    ⟨ha, k', hk, h.imp (fun h ↦ ⟨h.1, RunKB.mono hQ h.2⟩) id⟩

theorem RunKB.append {entry k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ {l₁ l₂ : List Item} {k : ℕ},
      RunKB S L fp prog entry k₀ (fun k' ↦ RunKB S L fp prog entry k₀ Q l₂ k') l₁ k →
        RunKB S L fp prog entry k₀ Q (l₁ ++ l₂) k
  | [], _, _, h => h
  | .ins _ :: _, _, _, ⟨ha, k', hk, h⟩ => ⟨ha, k', hk, RunKB.append h⟩
  | .fact _ :: _, _, _, ⟨ha, h⟩ => ⟨ha, RunKB.append h⟩
  | .branch _ _ _ _ :: _, _, _, ⟨ha, k', hk, h⟩ =>
    ⟨ha, k', hk, h.imp (fun h ↦ ⟨h.1, RunKB.append h.2⟩) id⟩

theorem FollowsB.append {entry : ℕ} {r : Semantics.Regs K} {Q : Prop} :
    ∀ {l₁ l₂ : List Item}, FollowsB S L fp entry r Q (l₁ ++ l₂) →
      FollowsB S L fp entry r (FollowsB S L fp entry r Q l₂) l₁
  | [], _, h => h
  | .ins _ :: l₁, _, ⟨ha, h⟩ => ⟨ha, FollowsB.append (l₁ := l₁) h⟩
  | .fact _ :: l₁, _, h => FollowsB.append (l₁ := l₁) h
  | .branch _ _ _ _ :: l₁, _, ⟨ha, h⟩ =>
    ⟨ha, h.imp (fun h ↦ ⟨h.1, FollowsB.append (l₁ := l₁) h.2⟩) id⟩

end Paths

/-! ## The pass: soundness and completeness -/

section Pass

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {entry len : ℕ}

variable (S) in
/-- **A good segment**: from its start, with its environment, it is sound (`RunKB`) and complete
(`FollowsB`), and `exits` lists its exits. -/
def SegGoodB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (s : Seg) : Prop :=
  (∀ k₀, EnvHolds L fp s.env → SafeB S prog L k₀ ⟨gpow (entry + s.start), fp⟩ →
    RunKB S L fp prog entry k₀ (s.exit.ReachedB S L fp prog entry k₀) s.items k₀) ∧
  (EnvHolds L fp s.env → ∀ r, FollowsB S L fp entry r (s.exit.kind.Regs L fp entry r) s.items →
    ReachB S prog L ⟨gpow (entry + s.start), fp⟩ r) ∧
  (∀ x, x = s.exit ∨ x ∈ branchExits s.items → x ∈ s.exits)

variable (S) in
/-- A good segment being walked, at offset `i`. -/
def CurGoodB (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (c : Cur) (i : ℕ) : Prop :=
  c.start ≤ i ∧ branchExits c.acc = c.xs ∧
  (∀ k₀, EnvHolds L fp c.env → SafeB S prog L k₀ ⟨gpow (entry + c.start), fp⟩ →
    RunKB S L fp prog entry k₀ (fun k ↦ k + i = k₀ + c.start ∧ St.HoldsB S L fp c.st ∧
      SafeB S prog L k ⟨gpow (entry + i), fp⟩) c.acc.reverse k₀) ∧
  (EnvHolds L fp c.env → ∀ r Q, FollowsB S L fp entry r Q c.acc.reverse →
    ReachB S prog L ⟨gpow (entry + c.start), fp⟩ r ∨
      (Q ∧ St.HoldsB S L fp c.st ∧ ReachB S prog L ⟨gpow (entry + c.start), fp⟩ ⟨gpow (entry + i), fp⟩))

theorem stHoldsB_init {env : Trie Sym} (he : EnvHolds L fp env) : St.HoldsB S L fp (St.init env) :=
  ⟨he, fun _ _ _ h ↦ by simp [St.init] at h, fun _ h ↦ by simp [St.init] at h⟩

theorem curGoodB_init (i : ℕ) (env : Trie Sym) : CurGoodB S L fp prog entry (Cur.init i env) i := by
  refine ⟨le_rfl, rfl, fun k₀ he hs ↦ ?_, fun he r Q hq ↦ Or.inr ⟨hq, stHoldsB_init he, ReachB.refl _⟩⟩
  exact ⟨by simp [Cur.init], stHoldsB_init he, hs⟩

theorem segGoodB_close {c : Cur} {i : ℕ} (hc : CurGoodB S L fp prog entry c i) (hlt : c.start < i)
    (succ : List ℕ) : SegGoodB S L fp prog entry (c.close [] ⟨.next i, c.st.env, succ⟩) := by
  obtain ⟨-, hxs, hsound, hcomp⟩ := hc
  refine ⟨fun k₀ he hs ↦ ?_, fun he r hf ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [Cur.close, items_close, List.append_nil]
    refine RunKB.mono (fun k ⟨hk, hst, hs'⟩ ↦ ⟨by omega, hst.1, trivial, _, rfl, hs'⟩)
      (hsound k₀ he hs)
  · simp only [Cur.close, items_close, List.append_nil] at hf
    rcases hcomp he r _ hf with h | ⟨rfl, -, h⟩
    · exact h
    · exact h
  · simp only [Cur.close] at hx ⊢
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      have := mem_branchExits_reverse hx
      rwa [branchExits_reverseAux, hxs] at this

theorem curGoodB_go (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurGoodB S L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {st : St}
    (hs : stepI F entry len i c.st ins = .go its st) :
    CurGoodB S L fp prog entry
      ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩ (i + 1) := by
  obtain ⟨hle, hxs, hsound, hcomp⟩ := hc
  refine ⟨show c.start ≤ i + 1 by omega, by simp only; rw [branchExits_reverseAux, hxs],
    fun k₀ he h0 ↦ ?_, fun he r Q hq ↦ ?_⟩
  · simp only
    rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]
    refine RunKB.append (RunKB.mono (fun k ⟨hk, hst, hs'⟩ ↦ ?_) (hsound k₀ he h0))
    have := stepIB_sound (len := len) (k₀ := k₀) hctx hf hpc hst (by omega) hs'
    rw [hs] at this
    refine RunKB.mono (fun k' ⟨hk', hst', hs''⟩ ↦ ⟨by omega, hst', ?_⟩) this
    simpa [Nat.add_assoc] using hs''
  · simp only at hq
    rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse] at hq
    rcases hcomp he r _ (FollowsB.append hq) with h | ⟨hq', hst, h⟩
    · exact Or.inl h
    · have := stepIB_complete (len := len) hctx hf hpc hst r
      rw [hs] at this
      rcases this Q hq' with h' | ⟨hQ, hst', h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨hQ, hst', by simpa [Nat.add_assoc] using h.trans h'⟩

theorem segGoodB_stop (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurGoodB S L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {x : Exit}
    (hs : stepI F entry len i c.st ins = .stop its x) : SegGoodB S L fp prog entry (c.close its x) := by
  obtain ⟨hle, hxs, hsound, hcomp⟩ := hc
  refine ⟨fun k₀ he h0 ↦ ?_, fun he r hq ↦ ?_, fun y hy ↦ ?_⟩
  · simp only [Cur.close, items_close]
    refine RunKB.append (RunKB.mono (fun k ⟨hk, hst, hs'⟩ ↦ ?_) (hsound k₀ he h0))
    have := stepIB_sound (len := len) (k₀ := k₀) hctx hf hpc hst (by omega) hs'
    rw [hs] at this
    exact this
  · simp only [Cur.close, items_close] at hq
    rcases hcomp he r _ (FollowsB.append hq) with h | ⟨hq', hst, h⟩
    · exact h
    · have := stepIB_complete (len := len) hctx hf hpc hst r
      rw [hs] at this
      exact h.trans (this hq')
  · simp only [Cur.close] at hy ⊢
    rcases hy with rfl | hy
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      have := mem_branchExits_reverse hy
      rwa [branchExits_reverseAux, hxs] at this

theorem atJoinB_good {i : ℕ} {cur : Option Cur} {pend : Pend} {out : List Seg}
    (hcur : ∀ c, cur = some c → CurGoodB S L fp prog entry c i)
    (hout : ∀ s ∈ out, SegGoodB S L fp prog entry s) :
    (∀ c, (atJoin i cur pend out).1 = some c → CurGoodB S L fp prog entry c i) ∧
      ∀ s ∈ (atJoin i cur pend out).2.2, SegGoodB S L fp prog entry s := by
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
            exact curGoodB_init i _
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact segGoodB_close (hcur c rfl) hlt [i]
            · exact hout s hs
        · refine ⟨fun c' hc' ↦ ?_, hout⟩
          obtain rfl := Option.some.inj hc'
          exact curGoodB_init i _
      | none =>
        simp only [Trie.seq_eq]
        refine ⟨fun c' hc' ↦ ?_, hout⟩
        obtain rfl := Option.some.inj hc'
        exact curGoodB_init i _
    · exact ⟨hcur, hout⟩
  · exact ⟨hcur, hout⟩

/-- **The walk produces good segments.** -/
theorem passB_good (hctx : Ctx F κ fp) : ∀ (code : List OInstr) (i : ℕ) (cur : Option Cur)
    (pend : Pend) (out : List Seg) (dead : ℕ), Fetches prog (entry + i) code →
    (∀ c, cur = some c → CurGoodB S L fp prog entry c i) →
    (∀ s ∈ out, SegGoodB S L fp prog entry s) →
    ∀ s ∈ (pass F entry len code i cur pend out dead).segs, SegGoodB S L fp prog entry s
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
        · exact segGoodB_close (hcur c rfl) hlt _
        · exact hout s hs
      · rw [ite_eq_right hlt]
        exact hout
  | ins :: rest, i, cur, pend, out, dead, hf, hcur, hout => by
    show ∀ s ∈ (passStep F entry len ins (pass F entry len rest) i cur pend out dead).segs, _
    obtain ⟨hcur', hout'⟩ := atJoinB_good (pend := pend) hcur hout
    have hrest : Fetches prog (entry + (i + 1)) rest := by
      simpa [Nat.add_assoc] using hf.tail
    obtain ⟨hfi, hpc⟩ := hf.head
    unfold passStep
    rcases hj : atJoin i cur pend out with ⟨cur', pend', out'⟩
    rw [hj] at hcur' hout'
    cases cur' with
    | none =>
      simp only [natSeq_eq]
      exact passB_good hctx rest (i + 1) none pend' out' (dead + 1) hrest (fun _ h ↦ by cases h)
        hout'
    | some c =>
      have hc := hcur' c rfl
      simp only
      rcases hs : stepI F entry len i c.st ins with ⟨its, st⟩ | ⟨its, x⟩
      · simp only [St.seq_eq, headSeq_eq, natSeq_eq]
        exact passB_good hctx rest (i + 1) _ _ out' dead hrest
          (fun c' h ↦ Option.some.inj h ▸ curGoodB_go hctx hc hfi hpc hs) hout'
      · simp only [headSeq_eq, natSeq_eq]
        refine passB_good hctx rest (i + 1) none _ _ dead hrest (fun _ h ↦ by cases h) ?_
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact segGoodB_stop hctx hc hfi hpc hs
        · exact hout' s hs'

end Pass

/-! ## The executor: soundness, completeness, linking -/

section Main

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {f : CompiledFn}

/-- Every segment of `exec F f` is good. -/
theorem execB_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) :
    ∀ s ∈ (exec F f).segs, SegGoodB S L fp prog f.entry s :=
  passB_good hctx f.code 0 _ [] [] 0 (by simpa using hf)
    (fun _ h ↦ Option.some.inj h ▸ curGoodB_init 0 _) (fun _ h ↦ by cases h)

/-- **Soundness**: a halting run entering a segment of `exec F f` at its start, in a frame its
environment holds of, satisfies every atom of the path it takes, one step per instruction, and
leaves by that path's exit (`Exit.ReachedB`: with fewer steps left, its environment holding,
at the registers its kind names). -/
theorem execB_sound (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) {k : ℕ} (he : EnvHolds L fp s.env)
    (h : SafeB S prog L k ⟨gpow (f.entry + s.start), fp⟩) :
    RunKB S L fp prog f.entry k (s.exit.ReachedB S L fp prog f.entry k) s.items k :=
  (execB_good hctx hf s hs).1 k he h

/-- **Completeness**: on a memory satisfying the atoms of a path of a segment, in a frame its
environment holds of, the run from the segment's start reaches the registers the path's exit
names. -/
theorem execB_complete (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) (he : EnvHolds L fp s.env) {r : Semantics.Regs K}
    (h : FollowsB S L fp f.entry r (s.exit.kind.Regs L fp f.entry r) s.items) :
    ReachB S prog L ⟨gpow (f.entry + s.start), fp⟩ r :=
  (execB_good hctx hf s hs).2.1 he r h

end Main

/-! ## Straight segments -/

section Straight

variable {κ : ℕ} {L : MemImage κ} {fp : K} {prog : Program}

/-- **A path without branches**: every atom holds, and the end is reached. -/
theorem RunKB.straight {entry k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ {its : List Item} {k : ℕ}, branchExits its = [] → RunKB S L fp prog entry k₀ Q its k →
      (∀ a ∈ its.filterMap Item.atom?, a.HoldsB S L fp) ∧ ∃ k' ≤ k, Q k'
  | [], k, _, h => ⟨fun _ h ↦ by simp at h, k, le_rfl, h⟩
  | .ins a :: its, _, hb, ⟨ha, k', rfl, h⟩ => by
    obtain ⟨hs, k'', hk, hq⟩ := RunKB.straight (its := its) hb h
    refine ⟨fun b hb' ↦ ?_, k'', by omega, hq⟩
    simp only [List.filterMap_cons, Item.atom?, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ha
    · exact hs b hb'
  | .fact a :: its, k, hb, ⟨ha, h⟩ => by
    obtain ⟨hs, k'', hk, hq⟩ := RunKB.straight (its := its) hb h
    refine ⟨fun b hb' ↦ ?_, k'', hk, hq⟩
    simp only [List.filterMap_cons, Item.atom?, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ha
    · exact hs b hb'
  | .branch _ _ _ _ :: _, _, hb, _ => by simp [branchExits] at hb

end Straight

/-! ## Windows -/

section Windows

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {f : CompiledFn}

/-- Every segment of a window is good. -/
theorem execWinB_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) (a : ℕ)
    (env : List (ℕ × Sym)) (b : ℕ) : ∀ s ∈ (execWin F f a env b).segs, SegGoodB S L fp prog f.entry s :=
  passB_good hctx _ a _ [] [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curGoodB_init a _) (fun _ h ↦ by cases h)

/-- **Soundness** on a window, as `execB_sound`. -/
theorem execWinB_sound (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {a b : ℕ}
    {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs) {k : ℕ}
    (he : EnvHolds L fp s.env) (h : SafeB S prog L k ⟨gpow (f.entry + s.start), fp⟩) :
    RunKB S L fp prog f.entry k (s.exit.ReachedB S L fp prog f.entry k) s.items k :=
  (execWinB_good hctx hf a env b s hs).1 k he h

/-- **Completeness** on a window, as `execB_complete`. -/
theorem execWinB_complete (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {a b : ℕ}
    {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs)
    (he : EnvHolds L fp s.env) {r : Semantics.Regs K}
    (h : FollowsB S L fp f.entry r (s.exit.kind.Regs L fp f.entry r) s.items) :
    ReachB S prog L ⟨gpow (f.entry + s.start), fp⟩ r :=
  (execWinB_good hctx hf a env b s hs).2.1 he r h

end Windows

end
end LeanVM.Guest.Exec
