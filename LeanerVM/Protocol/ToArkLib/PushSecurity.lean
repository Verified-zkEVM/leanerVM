/-
  LeanerVM.Protocol.ToArkLib.PushSecurity

  Round-by-round soundness of challenges drawn into a vector one at a time, for relations that do
  not read the witness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.SampleChallenge

/-!
# Security of pushed challenges

`Component.drawPushes` (`SampleChallenge`) draws `j` challenges one at a time and pushes each onto
a vector beside the statement; `drawPushesComplete` composes the completeness of the draws. This is
the security half, composed the same way, from a family of relations `rel j` on the statement with
the first `j` challenges and a bound `N` on the bad challenges of each draw: the first draw's
input is the relation at the empty vector, and the error of each is `N / |C|` (`drawsError`).

* `indep`, `card_badChallenge_le_of_indep`: relations that ignore the witness, and the count of
  bad challenges for them, as `card_badChallenge_le_of_unit` is for the trivial witness;
* `passThroughSecurityOfImp`: the pass-through component is secure at the empty error whenever the
  output relation at the mapped statement implies the input relation;
* `drawPushSecurity`, `drawPushesSecurity`: one pushed challenge, and the first `j ≤ n`.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Component

/-- A relation on statements and oracles, as a relation that ignores the witness. -/
def indep {ι : Type} (S : Type) (O : ι → Type) (W : Type) (R : S × (∀ i, O i) → Prop) :
    Set ((S × ∀ i, O i) × W) := {p | R p.1}

section Indep

variable {ι : Type} (OStmt : ι → Type) {S T : Type} (C : Type) [Finite C]

/-- With relations that ignore the witness, the bad challenges are those that carry a statement
outside the input relation into the output relation. -/
theorem card_badChallenge_le_of_indep [∀ i, OracleInterface (OStmt i)] [SampleableType C]
    {W : Type} (f : S → C → T) (RI : S × (∀ i, OStmt i) → Prop) (RO : T × (∀ i, OStmt i) → Prop)
    (N : ℕ) (s : S) (o : ∀ i, OStmt i)
    (h : ¬ RI (s, o) → Nat.card {c : C // RO (f s c, o)} ≤ N) :
    Nat.card {c : C // badChallenge OStmt C f (relIn := indep S OStmt W RI)
      (relOut := indep T OStmt W RO) s o c} ≤ N := by
  have := Fintype.ofFinite C
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hin : RI (s, o)
  · refine le_trans (le_of_eq ?_) (Nat.zero_le N)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨w, hw, -⟩
    exact hw hin
  · refine (Finset.card_le_card fun c hc ↦ ?_).trans
      ((natCard_subtype_eq_card_filter _).symm.trans_le (h hin))
    rw [Finset.mem_filter] at hc ⊢
    obtain ⟨-, w, -, hw⟩ := hc
    exact ⟨Finset.mem_univ _, hw⟩

end Indep

section PassThrough

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W : Type} (f : StmtIn → StmtOut)
  {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)} {relOut : Set ((StmtOut × ∀ i, OStmt i) × W)}
  (h : ∀ s o w, ((f s, o), w) ∈ relOut → ((s, o), w) ∈ relIn)

/-- The security half of the pass-through component, at error zero, with the extractor that keeps
the witness, whenever the output relation at the mapped statement implies the input relation. -/
def passThroughSecurityOfImp :
    Security (passThrough OStmt f) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := (passThroughPure OStmt f).toGuardedForm
  witMid := fun _ ↦ W
  extractor := keepExtractor (StmtIn × ∀ i, OStmt i) W !p[]
  kSF := passThroughStateFunction OStmt f h
  rbr := passThrough_rbr OStmt f h

end PassThrough

section Pushes

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)] (C : Type)
  [SampleableType C] [Finite C] {S W : Type}
  (rel : (j : ℕ) → Set (((S × Vector C j) × ∀ i, OStmt i) × W))

/-- The security half of one pushed challenge, at `N / |C|`, whenever at most `N` challenges
carry a statement outside the relation `j` into the relation `j + 1`. -/
def drawPushSecurity (j N : ℕ)
    (hN : ∀ s o, Nat.card {c : C // badChallenge OStmt C
      (fun (s : S × Vector C j) (x : C) ↦ (s.1, s.2.push x)) (relIn := rel j)
      (relOut := rel (j + 1)) s o c} ≤ N) :
    Security (drawPush (W := W) OStmt C j) (rel j) (rel (j + 1))
      (drawError C ((N : ℝ≥0) / (Nat.card C : ℝ≥0))) :=
  sampleChallengeSecurity OStmt C (fun _ ↦ true)
    (fun (s : S × Vector C j) (x : C) ↦ (s.1, s.2.push x)) N fun s o _ ↦ hN s o

/-- The security half of the first `j ≤ n` pushed challenges, each at `N / |C|`: the input
relation is the relation `0` at the empty vector, and for each challenge below `n` at most `N`
challenges carry a statement outside the relation before it into the relation after it. -/
def drawPushesSecurity (relIn : Set ((S × ∀ i, OStmt i) × W)) (n N : ℕ)
    (hIn : ∀ s o w, (((s, (#v[] : Vector C 0)), o), w) ∈ rel 0 → ((s, o), w) ∈ relIn)
    (hN : ∀ j < n, ∀ s o, Nat.card {c : C // badChallenge OStmt C
      (fun (s : S × Vector C j) (x : C) ↦ (s.1, s.2.push x)) (relIn := rel j)
      (relOut := rel (j + 1)) s o c} ≤ N) :
    (j : ℕ) → j ≤ n →
      Security (drawPushes (W := W) OStmt C j) relIn (rel j)
        (drawsError C ((N : ℝ≥0) / (Nat.card C : ℝ≥0)) j)
  | 0, _ => passThroughSecurityOfImp OStmt (fun s ↦ (s, (#v[] : Vector C 0))) hIn
  | j + 1, hj =>
    (drawPushesSecurity relIn n N hIn hN j (by omega)).append
      (drawPushSecurity OStmt C rel j N (hN j (by omega)))

end Pushes

end Component

end
end LeanerVM.Protocol
