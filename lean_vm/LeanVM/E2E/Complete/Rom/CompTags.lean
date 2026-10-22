/-
  LeanVM.E2E.Complete.Rom.CompTags

  T6-prob: the honest prover's failure tags. A proof-of-work failure is a failed search on the
  hash's answers (G1); vanishing weights vanish on the hash's answers (G2), of children of the
  bytecode's shapes, at most `16` of them.
-/

module

public import LeanVM.E2E.Complete.Rom.Comp
public import LeanVM.E2E.Complete.Rom.NonVacuityN
public import LeanVM.E2E.Complete.Rom.Kids
public import LeanVM.E2E.Complete.NonVacuity
public import LeanVM.E2E.Batch.Weights

/-!
# The failure tags

`docs/roadmap/t6-prob.md` §4.4. The honest prover with the hash an answering function
`L : Bytes → Option Digest` (`honestProverM`, at `m := Option`) fails, when it does, with a tag
that is true of `L`'s answers:

* `honestProverM_grind`: a `.grind P S seed` failure is V°'s program at some digest, and the
  honest prover's search from `seed` fails on `L` (`proveFromM … = some none`);
* `honestProverM_weights`: a `.weights cs` failure has at least one child, and the batching of
  `cs` from the guest's baked start ends, on `L`, with both weights zero at bytecode rounds of the
  bytecode's size (`weightsWith`; through `weightsWith_honestBatchM`, `honestBatchM`'s weights are
  `weightsWith`'s at its hints' rounds);
* `honestOutN_weights_children`, `honestOutN_weights_shaped` (`RomPieces.shaped`'s form): the
  H-oblivious prover's `.weights cs` failure has children of the bytecode's shapes, at least one
  and at most `16` of them on a tree of at most `16` children a node (`HonestTree.KidsLe16`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete
open LeanVM.Guest.Batch LeanVM.Guest.B1.Main LeanVM.E2E LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## `ExceptT ε Option` -/

section ExceptOpt

variable {ε α β : Type}

/-- A failure of a bind is the first computation's, or the continuation's at its value. -/
theorem exceptTOpt_bind_error {x : ExceptT ε Option α} {f : α → ExceptT ε Option β} {e : ε}
    (h : (x >>= f).run = some (.error e)) :
    x.run = some (.error e) ∨ ∃ a, x.run = some (.ok a) ∧ (f a).run = some (.error e) := by
  rw [ExceptT.run_bind] at h
  rcases hx : x.run with _ | ⟨e' | a⟩
  · rw [hx] at h; cases h
  · rw [hx] at h
    cases h
    exact .inl rfl
  · rw [hx] at h
    exact .inr ⟨a, rfl, h⟩

/-- A lifted computation, then a continuation: the continuation at its value. -/
theorem exceptTOpt_lift_bind (x : Option α) (f : α → ExceptT ε Option β) :
    ((ExceptT.lift x : ExceptT ε Option α) >>= f).run = x.bind fun a ↦ (f a).run := by
  cases x <;> rfl

/-- A `mapM` in `ExceptT ε Option` fails with one of its elements' failures. -/
theorem exceptTOpt_mapM_error {f : α → ExceptT ε Option β} :
    ∀ {l : List α} {e : ε}, (l.mapM f).run = some (.error e) → ∃ a ∈ l, (f a).run = some (.error e)
  | [], e, h => by simp at h
  | a :: l, e, h => by
    rw [List.mapM_cons] at h
    rcases exceptTOpt_bind_error h with h | ⟨b, -, h⟩
    · exact ⟨a, List.mem_cons_self, h⟩
    · rcases exceptTOpt_bind_error h with h | ⟨bs, -, h⟩
      · obtain ⟨a', ha', h'⟩ := exceptTOpt_mapM_error h
        exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
      · simp at h

/-- A `mapM` in `Option` keeps the length. -/
theorem optionMapM_length {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [optionMapM_length hbs]

end ExceptOpt

/-! ## The batching's weights with an answered hash -/

section Batch

variable (L : Bytes → Option Digest)

theorem sq2HM_option : ∀ (n : ℕ) (cv : Digest), sq2HM (m := Option) L n cv = sq2W L n cv
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sq2HM, sq2W, sq2HM_option n]

theorem sq3HM_option : ∀ (n : ℕ) (cv : Digest), sq3HM (m := Option) L n cv = sq3W L n cv
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sq3HM, sq3W, sq3HM_option n]

/-- The honest rounds have the round count's length. -/
theorem honestRoundsM_length (n : ℕ) (f : List E → E) :
    ∀ (k : ℕ) (pre : List E) (cv : Digest) {r : List (E × E)},
      honestRoundsM (m := Option) L n f k pre cv = some r → r.length = k
  | 0, _, _, r, h => by
    simp only [honestRoundsM] at h
    cases h
    rfl
  | k + 1, pre, cv, r, h => by
    simp only [honestRoundsM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨cv', -, rest, hrest, rfl⟩ := h
    simp [honestRoundsM_length n f k _ _ hrest]

/-- **The honest batching's weights are the answered weights at its hints' rounds**, and the
rounds have the bytecode's size. -/
theorem weightsWith_honestBatchM {s0 : Digest} {bc : List K} {cs : List ChildClaims}
    {w : E × E} {h : BatchHints} (hb : honestBatchM (m := Option) L s0 bc cs = some (w, h)) :
    weightsWith L s0 cs h.bytecodeRounds = some w ∧
      h.bytecodeRounds.length = Nat.log2 bc.length := by
  simp only [honestBatchM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hb
  obtain ⟨cvA, hA, b, hsq, rounds, hr, be, hbe, ms, hms, me, hme, hwh⟩ := hb
  simp only [Prod.mk.injEq] at hwh
  obtain ⟨rfl, rfl⟩ := hwh
  refine ⟨?_, honestRoundsM_length L _ _ _ _ _ hr⟩
  simp only [weightsWith, hintsOf, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
  rw [sq2HM_option] at hsq
  rw [sq3HM_option] at hms
  exact ⟨cvA, hA, b, hsq, be, hbe, ms, hms, me, hme, rfl⟩

end Batch

/-! ## The failures of the prover with an answered hash -/

section Tags

variable (L : Bytes → Option Digest) (ρ pfuel : ℕ)

/-- **A failure tag true of the answers `L`**: a search failed on `L` at V°'s program, or the
batching's weights vanish on `L`, of at least one child. -/
def ProverFailOn : ProverFail → Prop
  | .grind P S seed => (∃ pi, P = progOf pi) ∧ proveFromM L S pfuel P seed [] = some none
  | .weights cs => cs ≠ [] ∧ ∃ rounds : List (E × E),
      rounds.length = Nat.log2 End.bytecode.length ∧
        weightsWith L B1.Main.aggSeedD cs rounds = some (0, 0)
  | .stuck => True

/-- The children's claims keep the children's count. -/
theorem claimsOfM_length {cs : List Child} {ccs : List ChildClaims}
    (h : claimsOfM (m := Option) L cs = some ccs) : ccs.length = cs.length :=
  optionMapM_length h

/-- **The deferred claim's failures are tagged.** -/
theorem honestDeferM_tag {cs : List Child} {f : ProverFail}
    (h : (honestDeferM L cs).run = some (.error f)) : ProverFailOn L pfuel f := by
  unfold honestDeferM at h
  by_cases h0 : cs = []
  · simp only [h0, ↓reduceIte] at h
    cases h
  simp only [h0, ↓reduceIte] at h
  rcases exceptTOpt_bind_error h with h | ⟨ccs, hccs, h⟩
  · simp at h
  rcases exceptTOpt_bind_error h with h | ⟨wh, hwh, h⟩
  · simp at h
  have hccs' : claimsOfM (m := Option) L cs = some ccs := by
    revert hccs
    cases claimsOfM (m := Option) L cs with
    | none => intro hc; cases hc
    | some a => intro hc; cases hc; rfl
  have hwh' : honestBatchM (m := Option) L B1.Main.aggSeedD End.bytecode ccs = some wh := by
    revert hwh
    cases honestBatchM (m := Option) L B1.Main.aggSeedD End.bytecode ccs with
    | none => intro hc; cases hc
    | some a => intro hc; cases hc; rfl
  obtain ⟨wh', wh''⟩ := wh
  by_cases hz : wh' = (0, 0)
  · simp only [hz, ↓reduceIte, ExceptT.run_throw] at h
    cases h
    refine ⟨fun hn ↦ h0 (List.eq_nil_of_length_eq_zero (by
      rw [← claimsOfM_length L hccs', hn]; rfl)), ?_⟩
    obtain ⟨hw, hl⟩ := weightsWith_honestBatchM L hwh'
    exact ⟨_, hl, hz ▸ hw⟩
  · simp only [hz, ↓reduceIte] at h
    rcases exceptTOpt_bind_error h with h | ⟨r, -, h⟩
    · simp at h
    split at h
    · split at h
      · simp at h
      · simp only [ExceptT.run_throw] at h
        cases h
        trivial
    · simp only [ExceptT.run_throw] at h
      cases h
      trivial

/-- **A node's proof's failures are tagged.** -/
theorem proveNodeM_tag {s : NodeStatement} {w : NodeWitness} {kos : List HonestOutN}
    {f : ProverFail} (h : (proveNodeM L ρ pfuel s w kos).run = some (.error f)) :
    ProverFailOn L pfuel f := by
  unfold proveNodeM at h
  rcases exceptTOpt_bind_error h with h | ⟨pi, -, h⟩
  · simp at h
  rcases exceptTOpt_bind_error h with h | ⟨Lg, -, h⟩
  · simp at h
  split at h
  · simp only [ExceptT.run_throw] at h
    cases h
    trivial
  rename_i e he
  rcases exceptTOpt_bind_error h with h | ⟨seed, -, h⟩
  · simp at h
  rcases exceptTOpt_bind_error h with h | ⟨r, hr, h⟩
  · simp at h
  have hr' : proveM (m := Option) L (progOf pi) (stratOf ρ e) seed pfuel = some r := by
    revert hr
    cases proveM (m := Option) L (progOf pi) (stratOf ρ e) seed pfuel with
    | none => intro hc; cases hc
    | some a => intro hc; cases hc; rfl
  clear hr
  split at h
  · simp only [ExceptT.run_throw] at h
    cases h
    refine ⟨⟨pi, rfl⟩, ?_⟩
    simp only [proveM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr'
    obtain ⟨t, ht, hn⟩ := hr'
    cases t with
    | none => exact ht
    | some _ => cases hn
  rcases exceptTOpt_bind_error h with h | ⟨c, -, h⟩
  · simp at h
  split at h
  · simp only [ExceptT.run_throw] at h
    cases h
    trivial
  rcases exceptTOpt_bind_error h with h | ⟨kids, -, h⟩
  · simp at h
  · simp at h

/-- **The prover's failures are tagged**, on every subtree. -/
theorem honestProverM_tag :
    ∀ (T : HonestTree) {f : ProverFail}, (honestProverM L ρ pfuel T).run = some (.error f) →
      ProverFailOn L pfuel f := by
  refine HonestTree.induct' _ fun claims xs ss ds kids ih f h ↦ ?_
  rw [honestProverM] at h
  rcases exceptTOpt_bind_error h with h | ⟨kos, -, h⟩
  · obtain ⟨k, -, hk⟩ := exceptTOpt_mapM_error h
    exact ih k.1 k.2 hk
  unfold honestStepM at h
  rcases exceptTOpt_bind_error h with h | ⟨hd, -, h⟩
  · exact honestDeferM_tag L pfuel h
  · exact proveNodeM_tag L ρ pfuel h

end Tags

/-- **A failed search is a failed search on the hash's answers**, at V°'s program. -/
theorem honestProverM_grind {ρ pfuel : ℕ} {L : Bytes → Option Digest} {T : HonestTree}
    {P : Prog Bool} {S : Strategy} {seed : Digest}
    (h : (honestProverM L ρ pfuel T).run = some (.error (.grind P S seed))) :
    (∃ pi, P = progOf pi) ∧ proveFromM L S pfuel P seed [] = some none :=
  honestProverM_tag L ρ pfuel T h

/-- **Vanishing weights vanish on the hash's answers**: at least one child, and the batching from
the guest's baked start ends with both weights zero at bytecode rounds of the bytecode's size. -/
theorem honestProverM_weights {ρ pfuel : ℕ} {L : Bytes → Option Digest} {T : HonestTree}
    {cs : List ChildClaims} (h : (honestProverM L ρ pfuel T).run = some (.error (.weights cs))) :
    cs ≠ [] ∧ ∃ rounds : List (E × E), rounds.length = Nat.log2 End.bytecode.length ∧
      weightsWith L B1.Main.aggSeedD cs rounds = some (0, 0) :=
  honestProverM_tag L ρ pfuel T h

/-! ## The children of vanishing weights -/

section Shaped

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

/-- A node's proof never fails at the weights. -/
theorem proveNode_ne_weights {s : NodeStatement} {w : NodeWitness} {kos : List HonestOutN}
    {cs : List ChildClaims} : proveNode H ρ pfuel s w kos ≠ .error (.weights cs) := by
  unfold proveNode
  split
  · simp
  · split
    · simp
    · split <;> simp

/-- **The children of the H-oblivious prover's vanishing weights**: at least one, of the
bytecode's shapes, at most `16` of them, on a tree of at most `16` children a node. -/
theorem honestOutN_weights_children {T : HonestTree} {cs : List ChildClaims}
    (hρ : validRate ρ) (hk : T.AllNodes HonestTree.KidsLe16)
    (h : honestOutN H ρ pfuel T = .error (.weights cs)) :
    cs ≠ [] ∧ (∀ c ∈ cs, Guest.Batch.ChildShaped End.bytecode c) ∧ cs.length ≤ 16 := by
  revert hk h
  refine HonestTree.induct' (fun T ↦ T.AllNodes HonestTree.KidsLe16 →
    honestOutN H ρ pfuel T = .error (.weights cs) →
      cs ≠ [] ∧ (∀ c ∈ cs, Guest.Batch.ChildShaped End.bytecode c) ∧ cs.length ≤ 16)
    (fun claims xs ss ds kids ih hk h ↦ ?_) T
  rw [HonestTree.allNodes_node] at hk
  rw [honestOutN_node] at h
  cases hko : kidOutsN H ρ pfuel kids with
  | error f =>
    rw [hko] at h
    simp only [Except.bind] at h
    cases h
    obtain ⟨k, -, hf⟩ := mapM_error_mem hko
    exact ih k.1 k.2 (hk.2 k.1 k.2) hf
  | ok kos =>
    rw [hko] at h
    simp only [Except.bind] at h
    have h2 := forall₂_kidOutsN H ρ pfuel hko
    unfold honestStepN at h
    cases hdN : honestDeferN H (kos.map HonestOutN.child) with
    | ok hd =>
      rw [hdN] at h
      exact absurd h (proveNode_ne_weights H ρ pfuel)
    | error f =>
      rw [hdN] at h
      simp only [bind, Except.bind] at h
      cases h
      unfold honestDeferN at hdN
      by_cases h0 : kos.map HonestOutN.child = []
      · simp only [h0, ↓reduceIte] at hdN
        cases hdN
      by_cases hw : honestWeights H B1.Main.aggSeedD End.bytecode
          (childClaimsOf H (kos.map HonestOutN.child)) = (0, 0)
      · simp only [h0, hw, ↓reduceIte, Except.error.injEq, ProverFail.weights.injEq] at hdN
        subst hdN
        refine ⟨by simpa [childClaimsOf] using h0, ?_, ?_⟩
        · intro c hc
          simp only [childClaimsOf, List.map_map, List.mem_map, Function.comp_apply,
            HonestOutN.child] at hc
          obtain ⟨ko, hko', rfl⟩ := hc
          obtain ⟨k, -, hk'⟩ := forall₂_mem_right h2 ko hko'
          obtain ⟨hb, -, hacc, -⟩ := honestOutN_child H ρ pfuel hρ hk'
          refine ⟨verifyDeferredWith_shaped (fun x ↦ some (H x)) (bytecode := End.bytecode)
            (iv := seedOf H) (publicInput := digestOf H ko.stmt) (π := ko.proof) ?_, hb.1⟩
          rw [verifyDeferredWith_someH, hacc]
        · have hl := h2.length_eq
          simp only [childClaimsOf, List.length_map, ← hl]
          exact hk.1
      · simp only [h0, hw, ↓reduceIte] at hdN
        split at hdN
        · split at hdN
          · cases hdN
          · cases hdN
        · cases hdN

end Shaped

/-- **The children of the H-oblivious prover's vanishing weights have the bytecode's shapes**,
at most `16` of them, on a tree of at most `16` children a node (`RomPieces.shaped`). -/
theorem honestOutN_weights_shaped {ρ pfuel : ℕ} (hρ : validRate ρ) (H : Bytes → Digest)
    {T : HonestTree} {cs : List ChildClaims} (hk : T.AllNodes HonestTree.KidsLe16)
    (h : honestOutN H ρ pfuel T = .error (.weights cs)) :
    (∀ c ∈ cs, Guest.Batch.ChildShaped End.bytecode c) ∧ cs.length ≤ 16 :=
  (honestOutN_weights_children H ρ pfuel hρ hk h).2

end
end LeanVM.E2E.Complete
