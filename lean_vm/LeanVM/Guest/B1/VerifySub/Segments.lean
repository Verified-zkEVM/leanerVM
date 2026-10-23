/-
  LeanVM.Guest.B1.VerifySub.Segments

  An honest child's accepted deferring run, cut into the segments `verify_sub`'s callees run: the
  completeness direction of `Sound.lean`'s composition.
-/

module

public import LeanVM.Guest.B1.VerifySub.NZBridge
public import LeanVM.Guest.B1.VerifySub.CompleteSpec
public import LeanVM.Guest.B1.VerifySub.Sizes

/-!
# The segments of an honest child's run

`flatPre`: the deferring verifier's prefix grouped as `verify_sub` runs it (Split.lean's
`deferredFlat` up to the batching challenge): the announced sizes, the stack's root, the bus
challenges, the bus's GKR, `tablesSeg`, the lanes' check, `keccakSeg`, the ring map's other five
challenges; `specPre_flat`: it is `specPre`.

`runsTo_of_runF`: a carried run of a program without commitments is a `RunsTo` on the words it
reads. `readSizes_inv`: the announced sizes' run reads `eOfNat logMem`, the row counts, `eOfNat r`
and returns `layoutOf bytecode logMem rows` (the guest's bytecode of `2^23` words). `announced_eq`:
the run's sizes are `Verifier.announced`'s, so G7's bound `muMin ≤ stackLog` applies.

`child_segments`: on G7's per-child hypotheses, the child's stream is the concatenation of the
segments' words, each segment a carried run (`ChildSegs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The prefix, grouped as `verify_sub` runs it -/

/-- **The prefix, grouped as `verify_sub` runs it.** -/
def flatPre (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    Prog (Layout × ℕ × List StackClaim) :=
  (readSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (Prog.sampleN busBits).bind fun alphas ↦
  Prog.sampleE.bind fun beta ↦
  (Tables.gkrPhase (busLayout [0, ls.1.logMemory, ls.1.logBytecode] ls.1.push).depth).bind fun r ↦
  (Tables.tablesSeg (.claimed c) ls.1 pi alphas beta r.2.1 r.2.2).bind fun bc ↦
  (Prog.require ((lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)).bind fun _ ↦
  (keccakSeg (ls.1.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
    ((lanesOf bc.2).map (·.value))).bind fun km ↦
  (Prog.sampleN 5).bind fun chs ↦
  Prog.ret (ls.1, ls.2, stackClaims ls.1 bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs))

theorem specPre_flat (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    specPre (.claimed c) bytecode pi = flatPre c bytecode pi := by
  simp only [specPre, flatPre, restClaims, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
  refine congrArg _ (funext fun ls ↦ congrArg _ (funext fun _ ↦ ?_))
  rw [verifyBusBalance_split]
  simp only [Tables.tablesSeg, Prog.bind_assoc, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  refine congrArg _ (funext fun alphas ↦ congrArg _ (funext fun beta ↦ congrArg _ (funext fun r ↦
    congrArg _ (funext fun bus ↦ congrArg _ (funext fun cl ↦ congrArg _ (funext fun pc ↦ ?_))))))
  simp only [keccakPhase, lanesOf, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine congrArg _ (funext fun _ ↦ ?_)
  simp only [keccakSeg, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine congrArg _ (funext fun kr ↦ ?_)
  simp only [ringSwitch, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  rw [show ringMapShifts.length = 5 + 1 from rfl, Prog.sampleN]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
  refine congrArg _ (funext fun m ↦ congrArg _ (funext fun chs ↦ ?_))
  rfl


/-! ## Carried runs without commitments are `RunsTo` -/

/-- The deployed run from a carried one, on a sponge the start carries. -/
theorem runId_of_runF {α : Type} {p : Prog α} {st : Whir.FSt} {a : α} {st' : Whir.FSt}
    (h : Whir.runF p st = some (a, st')) {sp : Sponge} (hs : st.sponge.Carries sp) :
    ∃ sp', st'.sponge.Carries sp' ∧
      runId p ⟨sp, st.stream, st.openings, st.roots⟩ =
        some (a, ⟨sp', st'.stream, st'.openings, st'.roots⟩) := by
  rw [runF_eq_runT] at h
  obtain ⟨⟨a', t⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact Tables.runId_of_runT p (toT st) sp hs _ t ht

/-- A carried run keeps the words past what it reads, on any rest. -/
theorem runF_frame {α : Type} {p : Prog α} {st : Whir.FSt} {a : α} {st' : Whir.FSt}
    (h : Whir.runF p st = some (a, st')) :
    ∃ pre opre, st.stream = pre ++ st'.stream ∧ st.openings = opre ++ st'.openings ∧
      ∀ zs orest, Whir.runF p { st with stream := pre ++ zs, openings := opre ++ orest } =
        some (a, { st' with stream := zs, openings := orest }) := by
  rw [runF_eq_runT] at h
  obtain ⟨⟨a', t⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨pre, opre, hs, ho, hf⟩ := Tables.runT_frame p (toT st) a' t ht
  refine ⟨pre, opre, hs, ho, fun zs orest ↦ ?_⟩
  rw [runF_eq_runT]
  have e := hf zs orest
  simp only [toT] at e ⊢
  rw [e]
  rfl

theorem NoCommitA.runF_any {α : Type} (p : Prog α) : NoCommitA p → ∀ (s : Fs) (T : List E)
    (O : List Opening) (R : List (Digest × ℕ × ℕ)) (a : α) (st' : Whir.FSt),
    Whir.runF p ⟨s, T, O, R⟩ = some (a, st') →
      ∀ O2 R2, Whir.runF p ⟨s, T, O2, R2⟩ = some (a, { st' with openings := O2, roots := R2 }) := by
  induction p with
  | ret b =>
    intro _ s T O R a st' h O2 R2
    simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fail => intro _ s T O R a st' h; simp [Whir.runF] at h
  | read k ih =>
    intro hp s T O R a st' h O2 R2
    cases T with
    | nil => simp [Whir.runF] at h
    | cons x xs =>
      simp only [Whir.runF] at h ⊢
      exact ih x (hp x) _ xs O R a st' h O2 R2
  | sample k ih =>
    intro hp s T O R a st' h O2 R2
    exact ih _ (hp _) _ T O R a st' h O2 R2
  | grind b k ih =>
    intro hp s T O R a st' h O2 R2
    cases T with
    | nil => simp [Whir.runF] at h
    | cons n xs =>
      simp only [Whir.runF] at h ⊢
      split at h
      · rename_i hpow
        simp only [hpow, ↓reduceIte]
        exact ih hp _ xs O R a st' h O2 R2
      · simp at h
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **A carried run of a program without commitments is a `RunsTo`** on the words it reads. -/
theorem runsTo_of_runF {α : Type} {p : Prog α} (hp : NoCommit p) {s : Fs} {T : List E}
    {O : List Opening} {R : List (Digest × ℕ × ℕ)} {a : α} {st' : Whir.FSt}
    (h : Whir.runF p ⟨s, T, O, R⟩ = some (a, st')) :
    ∃ xs, T = xs ++ st'.stream ∧ RunsTo p s xs a st'.sponge := by
  obtain ⟨pre, opre, hs, ho, hf⟩ := runF_frame h
  obtain ⟨-, hO⟩ := NoCommit.runF hp h
  refine ⟨pre, hs, fun sp hsp rest os roots ↦ ?_⟩
  have e := hf rest []
  have e2 := NoCommitA.runF_any p ((noCommit_iff _).1 hp) s _ _ R a _ e os roots
  obtain ⟨sp', hc, hr⟩ := runId_of_runF e2 hsp
  exact ⟨sp', hc, hr⟩


/-! ## The announced sizes -/

theorem runF_readN : ∀ (n : ℕ) (st : Whir.FSt) (xs : List E) (st' : Whir.FSt),
    Whir.runF (Prog.readN n) st = some (xs, st') →
      st.stream = xs ++ st'.stream ∧ xs.length = n
  | 0, st, xs, st', h => by
    simp only [Prog.readN, Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, st, xs, st', h => by
    simp only [Prog.readN, Prog.bind_eq, Prog.pure_eq] at h
    obtain ⟨x, s1, h1, h⟩ := Whir.runF_bind_some h
    obtain ⟨ys, s2, h2, h⟩ := Whir.runF_bind_some h
    simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e2, l2⟩ := runF_readN n s1 ys s2 h2
    obtain ⟨sp, stream, os, R⟩ := st
    cases stream with
    | nil => simp [Prog.readE, Whir.runF] at h1
    | cons y rest =>
      simp only [Prog.readE, Whir.runF, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      refine ⟨?_, by simp [l2]⟩
      simp only at e2 ⊢
      rw [e2, List.cons_append]

theorem runF_liftOption_bind {α β : Type} {o : Option α} {k : α → Prog β} {st : Whir.FSt}
    {r : β × Whir.FSt} (h : Whir.runF ((liftOption o).bind k) st = some r) :
    ∃ a, o = some a ∧ Whir.runF (k a) st = some r := by
  cases o with
  | none => simp [Verifier.liftOption, Prog.bind, Whir.runF] at h
  | some a => exact ⟨a, rfl, h⟩

theorem word_eOfNat_of {v : E} (h1 : v.limb 1 = 0) (h2 : v.limb 2 = 0) :
    v = eOfNat (kToNat (v.limb 0)) := by
  apply E.ext
  intro i
  fin_cases i
  · simp [eOfNat, ofBits_kToNat]
  · simp [eOfNat, h1]
  · simp [eOfNat, h2]

/-- **The announced sizes' run**: the words `eOfNat logMem`, the row counts, `eOfNat r`, and the
layout `layoutOf bytecode logMem rows`. -/
theorem readSizes_inv {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {st : Whir.FSt}
    {L : Layout} {r : ℕ} {st' : Whir.FSt}
    (h : Whir.runF (readSizes bytecode) st = some ((L, r), st')) :
    ∃ (logMem : ℕ) (rowsN : List ℕ),
      st.stream = (eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat r]) ++ st'.stream ∧
      L = Tables.layoutOf bytecode logMem rowsN ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧
      rowsN.length = 6 ∧ (∀ n ∈ rowsN, n ≤ 2 ^ 32) ∧ 1 ≤ r ∧ r ≤ 4 ∧
      minStackedLog ≤ L.stackLog ∧ L.stackLog ≤ maxStackedLog := by
  unfold readSizes at h
  simp only [Prog.bind_eq, Prog.pure_eq] at h
  obtain ⟨xs, s1, h1, h⟩ := Whir.runF_bind_some h
  obtain ⟨hs1, hl⟩ := runF_readN _ _ _ _ h1
  obtain ⟨hall, h⟩ := runF_require_bind h
  obtain ⟨hr, h⟩ := runF_require_bind h
  obtain ⟨L', hL', h⟩ := runF_liftOption_bind h
  obtain ⟨hst, h⟩ := runF_require_bind h
  simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have hl8 : xs.length = 8 := by rw [hl]; rfl
  match xs, hl8, hall, hs1, hL', hr with
  | [v0, v1, v2, v3, v4, v5, v6, v7], _, hall, hs1, hL', hr =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      at hall
    obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩⟩ :=
      hall
    set rowsN := [kToNat (v1.limb 0), kToNat (v2.limb 0), kToNat (v3.limb 0), kToNat (v4.limb 0),
      kToNat (v5.limb 0), kToNat (v6.limb 0)] with hrowsN
    have hrows : ((([v0, v1, v2, v3, v4, v5, v6, v7].drop 1).take tables.length).map
        fun value ↦ kToNat (value.limb 0)) = rowsN := rfl
    have e7 : [v0, v1, v2, v3, v4, v5, v6, v7].getLastD 0 = v7 := rfl
    simp only [List.headD_cons, hrows, e7] at hL' hr hst ⊢
    -- the layout's conditions
    have hcond := hL'
    unfold buildLayout at hcond
    rw [hbl, show log2Strict (2 ^ 23) = some 23 by decide] at hcond
    simp only at hcond
    split at hcond
    · rename_i hc
      obtain ⟨-, h16, h32, hall32, -, hlen⟩ := hc
      have hlen' : rowsN.length = 6 := by rw [hlen]; rfl
      have hr32 : ∀ n ∈ rowsN, n ≤ 2 ^ 32 := by simpa using hall32
      have hLe := buildLayout_eq hbl h16 h32 hlen' hr32
      rw [hL'] at hLe
      obtain rfl := Option.some.inj hLe
      refine ⟨kToNat (v0.limb 0), rowsN, ?_, rfl, h16, h32, hlen', hr32, hr.1, hr.2, hst.1, hst.2⟩
      rw [hs1, ← word_eOfNat_of a0 b0, ← word_eOfNat_of a7 b7]
      simp only [hrowsN, List.map_cons, List.map_nil, ← word_eOfNat_of a1 b1,
        ← word_eOfNat_of a2 b2, ← word_eOfNat_of a3 b3, ← word_eOfNat_of a4 b4,
        ← word_eOfNat_of a5 b5, ← word_eOfNat_of a6 b6]
      rfl
    · simp at hcond


/-! ## The announced sizes are `Verifier.announced`'s -/

/-- Only reads (the run is a parse of the stream). -/
def ReadOnlyA {α : Type} : Prog α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, ReadOnlyA (k x)
  | .sample _ => False
  | .grind _ _ => False
  | .commit _ _ _ => False
  | .query _ _ _ => False

/-- **Only reads.** Irreducible, as `NoCommit`. -/
@[irreducible] def ReadOnly {α : Type} (p : Prog α) : Prop := ReadOnlyA p

theorem readOnly_iff {α : Type} (p : Prog α) : ReadOnly p ↔ ReadOnlyA p := by
  unfold ReadOnly; rfl

theorem ReadOnly.bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : ReadOnly p)
    (hf : ∀ a, ReadOnly (f a)) : ReadOnly (p.bind f) := by
  rw [readOnly_iff] at hp ⊢
  have hf' : ∀ a, ReadOnlyA (f a) := fun a ↦ (readOnly_iff _).1 (hf a)
  clear hf
  induction p with
  | ret a => exact hf' a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample _ _ => exact hp.elim
  | grind _ _ _ => exact hp.elim
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem readOnly_ret {α : Type} (a : α) : ReadOnly (Prog.ret a) := (readOnly_iff _).2 trivial

theorem readOnly_fail {α : Type} : ReadOnly (Prog.fail : Prog α) := (readOnly_iff _).2 trivial

theorem readOnly_readN : ∀ n, ReadOnly (Prog.readN n)
  | 0 => readOnly_ret _
  | n + 1 => by
    simp only [Prog.readN, Prog.bind_eq, Prog.pure_eq]
    refine ReadOnly.bind ((readOnly_iff _).2 fun _ ↦ trivial) fun _ ↦ ?_
    exact ReadOnly.bind (readOnly_readN n) fun _ ↦ readOnly_ret _

theorem readOnly_require (c : Prop) [Decidable c] : ReadOnly (Prog.require c) := by
  unfold Prog.require
  split
  · exact readOnly_ret _
  · exact readOnly_fail

theorem readOnly_liftOption {α : Type} (o : Option α) : ReadOnly (Verifier.liftOption o) := by
  cases o
  · exact readOnly_fail
  · exact readOnly_ret _

theorem readOnly_readSizes (bytecode : List K) : ReadOnly (readSizes bytecode) := by
  unfold readSizes
  simp only [Prog.bind_eq, Prog.pure_eq]
  refine ReadOnly.bind (readOnly_readN _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_require _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_require _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_liftOption _) fun _ ↦ ?_
  refine ReadOnly.bind (readOnly_require _) fun _ ↦ ?_
  exact readOnly_ret _

/-- A run that only reads returns what the stream gives, whatever the hashes and the sponge. -/
theorem ReadOnlyA.run_eq {α : Type} (p : Prog α) : ReadOnlyA p →
    ∀ (H H' : Bytes → Id Digest) (F F' : KState → Id KState) (sp sp' : Sponge) (T : List E)
      (O O' : List Opening) (R R' : List (Digest × ℕ × ℕ)),
      (Id.run (Compile.run (m := Id) H F p ⟨sp, T, O, R⟩)).map (·.1) =
        (Id.run (Compile.run (m := Id) H' F' p ⟨sp', T, O', R'⟩)).map (·.1) := by
  induction p with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro hp H H' F F' sp sp' T O O' R R'
    cases T with
    | nil => rfl
    | cons x xs => exact ih x (hp x) H H' F F' _ _ xs O O' R R'
  | sample _ _ => intro hp; exact hp.elim
  | grind _ _ _ => intro hp; exact hp.elim
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **The run's sizes are `Verifier.announced`'s.** -/
theorem announced_eq {bytecode : List K} {s : Fs} {T : List E} {O : List Opening}
    {R : List (Digest × ℕ × ℕ)} {L : Layout} {r : ℕ} {st' : Whir.FSt} {sp : Sponge}
    (hs : s.Carries sp) (h : Whir.runF (readSizes bytecode) ⟨s, T, O, R⟩ = some ((L, r), st')) :
    Verifier.announced bytecode T = some (L, r) := by
  obtain ⟨sp', -, hr⟩ := runId_of_runF h hs
  have e := ReadOnlyA.run_eq _ ((readOnly_iff _).1 (readOnly_readSizes bytecode))
    (fun _ ↦ pure default) keccak256 (fun _ ↦ pure default) keccakF ⟨default, []⟩ sp T [] O [] R
  unfold Verifier.announced
  rw [e]
  change (runId (readSizes bytecode) ⟨sp, T, O, R⟩).map (·.1) = _
  rw [hr]
  rfl

end
end LeanVM.Guest.B1.VerifySub
