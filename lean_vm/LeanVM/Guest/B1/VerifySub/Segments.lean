/-
  LeanVM.Guest.B1.VerifySub.Segments

  An honest child's accepted deferring run, cut into the segments `verify_sub`'s callees run: the
  completeness direction of `Sound.lean`'s composition.
-/

module

public import LeanVM.Guest.B1.VerifySub.NZBridge
public import LeanVM.Guest.B1.VerifySub.CompleteSpec

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

end
end LeanVM.Guest.B1.VerifySub
