/-
  LeanerVM.Protocol.ToArkLib.CachedProver

  An honest prover that carries prover-only data from one component to the next, beside the
  witness, and runs as the component's honest prover: its definition, its composition, the
  cached forms of the one-round components, and the transfer of completeness to the component
  with that prover and the same verifier. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.SendChecked
public import LeanerVM.Protocol.ToArkLib.SampleChallenge
public import LeanerVM.Protocol.ToArkLib.PassThrough
public import ArkLib.OracleReduction.Composition.Sequential.Append.Execution

/-!
# Cached honest provers

The honest prover of a component reads nothing but the statement, the oracles and the witness:
two components in sequence share only what the first hands the second. A prover that builds a
table once and reads it in every later round, the bound tables of a sumcheck or the levels of a
product tree, needs to hand it on, and a cache beside the witness is the place: the verifier
never sees it.

`Component.Cached D cin cout` is a prover for `D`'s schedule whose witness carries a cache, of
type `CIn` before and `COut` after, and whose run from the cache `cin` of its input is `D`'s
honest run with the cache `cout` of the output beside the output witness (`run_eq`). The two
functions say what the cache holds; they are never computed by the prover, which builds its
cache incrementally. Cached provers compose (`Cached.append`, by ArkLib's `Prover.append_run`),
take a cache built from the statement (`Cached.adaptIn`), and exist for every component with no
cache at all (`Cached.ofDef`). The one-round components have cached forms that read the message
from the cache and update it at the challenge (`Cached.sendChecked`, `Cached.sample`,
`Cached.passThrough`).

A cached prover with no cache on either side is a prover for `D`'s statements and witnesses
(`Cached.toProver`) whose run is `D`'s honest run (`Cached.toProver_run`): an honest-prover
refinement. The component with that prover and `D`'s verifier (`Cached.toDef`) is complete
whenever `D` is (`Cached.complete`), and has `D`'s verifier, so every guarded form and
knowledge-soundness proof of `D` is one of it. No definition changes.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-! ## Adapting a prover's input and output -/

section Adapt

variable {ι : Type} {oSpec : OracleSpec ι} {S₁ W₁ S₂ W₂ S₃ W₃ S₄ W₄ : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}

/-- A prover with its input mapped by `fIn` before it starts and its output by `fOut` after it
ends; its rounds are `P`'s. -/
def adaptProver (fIn : S₁ × W₁ → S₂ × W₂) (fOut : S₃ × W₃ → S₄ × W₄)
    (P : Prover oSpec S₂ W₂ S₃ W₃ pSpec) : Prover oSpec S₁ W₁ S₄ W₄ pSpec where
  PrvState := P.PrvState
  input := fun x ↦ P.input (fIn x)
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := fun st ↦ fOut <$> P.output st

/-- The adapted prover reaches every round as `P` does from the mapped input. -/
theorem adaptProver_runToRound (fIn : S₁ × W₁ → S₂ × W₂) (fOut : S₃ × W₃ → S₄ × W₄)
    (P : Prover oSpec S₂ W₂ S₃ W₃ pSpec) (i : Fin (n + 1)) (s : S₁) (w : W₁) :
    (adaptProver fIn fOut P).runToRound i s w = P.runToRound i (fIn (s, w)).1 (fIn (s, w)).2 :=
  rfl

/-- The run of the adapted prover: `P`'s run from the mapped input, its output mapped. -/
theorem adaptProver_run (fIn : S₁ × W₁ → S₂ × W₂) (fOut : S₃ × W₃ → S₄ × W₄)
    (P : Prover oSpec S₂ W₂ S₃ W₃ pSpec) (s : S₁) (w : W₁) :
    (adaptProver fIn fOut P).run s w =
      (fun r ↦ (r.1, fOut r.2)) <$> P.run (fIn (s, w)).1 (fIn (s, w)).2 := by
  simp only [Prover.run, adaptProver_runToRound, map_bind, map_pure]
  refine bind_congr fun r ↦ ?_
  simp only [adaptProver, liftM_map, bind_map_left]

end Adapt

namespace Component

variable {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn : Type}
  {StmtOut : Type} {ιo : Type} {OStmtOut : ιo → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]

/-! ## Cached provers -/

/-- A cached honest prover of `D`: a prover at `D`'s schedule whose witness carries a cache, and
whose run from the cache `cin` of its input is `D`'s honest run, with the cache `cout` of the
output beside the output witness. -/
structure Cached (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) {CIn COut : Type}
    (cin : (StmtIn × ∀ i, OStmtIn i) × WitIn → CIn)
    (cout : (StmtOut × ∀ i, OStmtOut i) × WitOut → COut) where
  /-- The prover, the cache beside the witness. -/
  prover : OracleProver []ₒ StmtIn OStmtIn (WitIn × CIn) StmtOut OStmtOut (WitOut × COut) pSpec
  /-- From the cache of its input, it runs as the honest prover, handing on the cache of its
  output. -/
  run_eq : ∀ s w, prover.run s (w, cin (s, w)) =
    (fun r ↦ (r.1, r.2.1, (r.2.2, cout r.2))) <$> D.red.prover.run s w

variable {D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}

/-- Every component has a cached prover with no cache: its honest prover. -/
def Cached.ofDef (D : Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    Cached D (fun _ ↦ ()) (fun _ ↦ ()) where
  prover := adaptProver (fun x ↦ (x.1, x.2.1)) (fun y ↦ (y.1, (y.2, ()))) D.red.prover
  run_eq s w := by
    rw [adaptProver_run]

/-- A cached prover started from a cache computed from its input, here `g` of the input and of a
cache `cin'` hands it, as long as `g` computes `cin` from `cin'`. -/
def Cached.adaptIn {CIn CIn' COut : Type} {cin : (StmtIn × ∀ i, OStmtIn i) × WitIn → CIn}
    {cout : (StmtOut × ∀ i, OStmtOut i) × WitOut → COut}
    {cin' : (StmtIn × ∀ i, OStmtIn i) × WitIn → CIn'}
    (g : (StmtIn × ∀ i, OStmtIn i) × WitIn → CIn' → CIn) (hg : ∀ p, g p (cin' p) = cin p)
    (Q : Cached D cin cout) : Cached D cin' cout where
  prover := adaptProver (fun x ↦ (x.1, (x.2.1, g (x.1, x.2.1) x.2.2))) id Q.prover
  run_eq s w := by
    rw [adaptProver_run]
    simp only [hg, id_eq, Prod.mk.eta, id_map']
    exact Q.run_eq s w

/-! ## Composition -/

variable {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
  [∀ i, OracleInterface (OStmt₃ i)]
  {m₁ m₂ : ℕ} {pSpec₁ : ProtocolSpec m₁} {pSpec₂ : ProtocolSpec m₂}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, OracleInterface (pSpec₂.Message i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {D₁ : Def Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁}
  {D₂ : Def Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂}
  {C₁ C₂ C₃ : Type} {c₁ : (Stmt₁ × ∀ i, OStmt₁ i) × Wit₁ → C₁}
  {c₂ : (Stmt₂ × ∀ i, OStmt₂ i) × Wit₂ → C₂} {c₃ : (Stmt₃ × ∀ i, OStmt₃ i) × Wit₃ → C₃}

/-- Cached provers compose: the first hands the second the cache of the statement between
them. -/
def Cached.append (Q₁ : Cached D₁ c₁ c₂) (Q₂ : Cached D₂ c₂ c₃) :
    Cached (D₁.append D₂) c₁ c₃ where
  prover := Q₁.prover.append Q₂.prover
  run_eq s w := by
    rw [Prover.append_run, Q₁.run_eq]
    change _ = _ <$> (D₁.red.prover.append D₂.red.prover).run s w
    rw [Prover.append_run]
    simp only [liftM_map, bind_map_left, map_bind]
    refine bind_congr fun r ↦ ?_
    obtain ⟨tr₁, s₂, w₂⟩ := r
    simp only [Q₂.run_eq, liftM_map, bind_map_left, map_pure]

/-! ## The one-round components, cached -/

section Send

variable (O : ιi → Type) [∀ i, OracleInterface (O i)] {S T W : Type} (M : Type)
  {CIn COut : Type} (msg : (S × ∀ i, O i) × W → CIn → M)
  (upd : (S × ∀ i, O i) × W → CIn → M → COut) (out : S → M → T)

/-- The cached prover of a checked message: the message read off the cache, the cache updated
by it. The message is computed once. -/
def cachedSendProver : OracleProver []ₒ S O (W × CIn) T O (W × COut) (say M) where
  PrvState
    | ⟨0, _⟩ => (S × ∀ i, O i) × (W × CIn)
    | _ => ((S × ∀ i, O i) × (W × CIn)) × M
  input := _root_.id
  sendMessage | ⟨0, _⟩ => fun st ↦ let m := msg (st.1, st.2.1) st.2.2; pure (m, (st, m))
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦
    pure ((out st.1.1.1 st.2, st.1.1.2), (st.1.2.1, upd (st.1.1, st.1.2.1) st.1.2.2 st.2))

variable {O M msg upd out} {honest : (S × ∀ i, O i) × W → M} {check : S → M → Bool}
  {cin : (S × ∀ i, O i) × W → CIn} {cout : (T × ∀ i, O i) × W → COut}

/-- The cached form of `Component.sendChecked`: the message read off the cache, which must be the
honest message, and the cache handed on updated by it, which must be the cache of the output. -/
def Cached.sendChecked (hmsg : ∀ p, msg p (cin p) = honest p)
    (hupd : ∀ p, upd p (cin p) (honest p) = cout ((out p.1.1 (honest p), p.1.2), p.2)) :
    Cached (Component.sendChecked O M honest check out) cin cout where
  prover := cachedSendProver O M msg upd out
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedSendProver, Component.sendChecked, Component.sendCheckedProver, _root_.id,
      hmsg, hupd]

/-- `Cached.sendChecked` with the output statement computed by `out'`, equal to `out`: a
statement whose fields the next components read many times can be built once. -/
def Cached.sendCheckedOut (out' : S → M → T) (hout : ∀ s m, out' s m = out s m)
    (hmsg : ∀ p, msg p (cin p) = honest p)
    (hupd : ∀ p, upd p (cin p) (honest p) = cout ((out p.1.1 (honest p), p.1.2), p.2)) :
    Cached (Component.sendChecked O M honest check out) cin cout where
  prover := cachedSendProver O M msg upd out'
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedSendProver, Component.sendChecked, Component.sendCheckedProver, _root_.id,
      hmsg, hupd, hout]

end Send

section Sample

variable (O : ιi → Type) [∀ i, OracleInterface (O i)] {S T W : Type} (C : Type)
  [SampleableType C] {CIn COut : Type} (upd : (S × ∀ i, O i) × W → CIn → C → COut)
  (f : S → C → T)

/-- The cached prover of a challenge: the cache updated by the challenge. -/
def cachedSampleProver : OracleProver []ₒ S O (W × CIn) T O (W × COut) (draw C) where
  PrvState
    | ⟨0, _⟩ => (S × ∀ i, O i) × (W × CIn)
    | _ => ((S × ∀ i, O i) × (W × CIn)) × C
  input := _root_.id
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun st ↦ pure fun c ↦ (st, c)
  output := fun st ↦
    pure ((f st.1.1.1 st.2, st.1.1.2), (st.1.2.1, upd (st.1.1, st.1.2.1) st.1.2.2 st.2))

variable {O C upd f} {check : S → Bool} {cin : (S × ∀ i, O i) × W → CIn}
  {cout : (T × ∀ i, O i) × W → COut}

/-- The cached form of `Component.sampleChallenge`: the cache handed on updated by the challenge,
which must give the cache of the output at every challenge. -/
def Cached.sample (hupd : ∀ p c, upd p (cin p) c = cout ((f p.1.1 c, p.1.2), p.2)) :
    Cached (Component.sampleChallenge O C check f) cin cout where
  prover := cachedSampleProver O C upd f
  run_eq s w := by
    have h0 : (draw C).dir 0 = .V_to_P := rfl
    simp only [Prover.run, Prover.runToRound, Fin.induction_one,
      Prover.processRound_of_dir_eq_V_to_P 0 h0, map_bind, map_pure, pure_bind, bind_assoc]
    refine bind_congr fun c ↦ ?_
    simp only [cachedSampleProver, sampleChallenge, sampleProver, pure_bind, liftM_pure,
      Fin.isValue]
    simp only [_root_.id, hupd]

/-- `Cached.sample` with the output statement computed by `f'`, equal to `f`: a statement whose
fields are read many times can be built by a faster function. -/
def Cached.sampleOut (f' : S → C → T) (hf : ∀ s c, f' s c = f s c)
    (hupd : ∀ p c, upd p (cin p) c = cout ((f p.1.1 c, p.1.2), p.2)) :
    Cached (Component.sampleChallenge O C check f) cin cout where
  prover := cachedSampleProver O C upd f'
  run_eq s w := by
    have h0 : (draw C).dir 0 = .V_to_P := rfl
    simp only [Prover.run, Prover.runToRound, Fin.induction_one,
      Prover.processRound_of_dir_eq_V_to_P 0 h0, map_bind, map_pure, pure_bind, bind_assoc]
    refine bind_congr fun c ↦ ?_
    simp only [cachedSampleProver, sampleChallenge, sampleProver, pure_bind, liftM_pure,
      Fin.isValue]
    simp only [_root_.id, hupd, hf]

end Sample

section PassThrough

variable (O : ιi → Type) [∀ i, OracleInterface (O i)] {S T W : Type} {CIn COut : Type}
  (upd : (S × ∀ i, O i) × W → CIn → COut) (f : S → T)

/-- The cached prover with no round: the statement mapped, the cache updated. -/
def cachedPassProver : OracleProver []ₒ S O (W × CIn) T O (W × COut) !p[] where
  PrvState := fun _ ↦ (S × ∀ i, O i) × (W × CIn)
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦ pure ((f p.1.1, p.1.2), (p.2.1, upd (p.1, p.2.1) p.2.2))

variable {O upd f} {cin : (S × ∀ i, O i) × W → CIn} {cout : (T × ∀ i, O i) × W → COut}

/-- The cached form of `Component.passThrough`. -/
def Cached.passThrough (hupd : ∀ p, upd p (cin p) = cout ((f p.1.1, p.1.2), p.2)) :
    Cached (Component.passThrough (W := W) O f) cin cout where
  prover := cachedPassProver O upd f
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedPassProver, Component.passThrough, Component.passThroughProver, _root_.id,
      hupd]

end PassThrough

/-! ## The refined component -/

/-- A cached prover with no cache on either side, as a prover of `D`'s statements and
witnesses. -/
def Cached.toProver (Q : Cached D (fun _ ↦ ()) (fun _ ↦ ())) :
    OracleProver []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec :=
  adaptProver (fun x ↦ (x.1, (x.2, ()))) (fun y ↦ (y.1, y.2.1)) Q.prover

/-- **Honest-prover refinement.** The prover runs as `D`'s honest prover. -/
theorem Cached.toProver_run (Q : Cached D (fun _ ↦ ()) (fun _ ↦ ())) (s : StmtIn × ∀ i, OStmtIn i)
    (w : WitIn) : Q.toProver.run s w = D.red.prover.run s w := by
  rw [Cached.toProver, adaptProver_run]
  change _ <$> Q.prover.run s (w, (fun _ ↦ ()) (s, w)) = _
  rw [Q.run_eq, Functor.map_map]
  exact id_map _

/-- The component with the cached prover and `D`'s verifier. -/
def Cached.toDef (Q : Cached D (fun _ ↦ ()) (fun _ ↦ ())) :
    Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec where
  red := ⟨Q.toProver, D.red.verifier⟩

/-- The refined component's runs are `D`'s. -/
theorem Cached.toDef_run (Q : Cached D (fun _ ↦ ()) (fun _ ↦ ())) (s : StmtIn × ∀ i, OStmtIn i)
    (w : WitIn) : Q.toDef.red.toReduction.run s w = D.red.toReduction.run s w := by
  simp only [Reduction.run]
  exact congrArg (· >>= _) (congrArg OptionT.lift (Q.toProver_run s w))

/-- The refined component is complete wherever `D` is: the same verifier, the same runs. -/
def Cached.complete (Q : Cached D (fun _ ↦ ()) (fun _ ↦ ()))
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)} (C : Complete D relIn relOut) :
    Complete Q.toDef relIn relOut where
  guarded := C.guarded
  complete init impl := by
    have h := C.complete init impl
    unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness
      Reduction.completeness at h ⊢
    intro s w hin
    rw [Q.toDef_run]
    exact h s w hin

end Component

end
end LeanerVM.Protocol
