/-
  LeanVM.Guest.B1.Main.TablesAtS

  `TablesAt.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.TablesAt
public import LeanVM.Guest.B1.Main.LoopAtS

/-!
# `TablesAt.lean` under any `BLAKE2S` semantics

Each definition and lemma of `TablesAt.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB etBody etBlk1 etBlk2 core2_body find_exponent_tables
  holdsList_range_flatten word_eOfNat)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem etS_holds {C : CallRel} {rd : Reader} {p q : E} (ht : ExpTables rd p q) :
    Stmt.HoldsListB S C rd (etVal p q) etBody False (fun rs => rs = [p, q]) := by
  rw [etBody]
  simp only [holdsListB_append, Stmt.HoldsListB]
  simp only [holdsListB_flatten_range 34 etBlk1 (fun _ => rfl),
    holdsListB_flatten_range 34 etBlk2 (fun _ => rfl), etBlk1, etBlk2]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, true_and,
    and_true]
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
  all_goals (try (simp only [etVal]; b1_look))
  · rw [word_eOfNat]; exact ⟨trivial, (ht j hj).1⟩
  · rw [word_eOfNat, eOfNat_gSquaresBits j hj]; exact ⟨trivial, (ht j hj).2⟩

set_option maxRecDepth 100000 in
/-- **`exponent_tables` at `fp`**, on every memory holding its two tables at
`b = fp + fs "exponent_tables"` and `b + 34`, which the caller may read afterwards. -/
theorem exponentS_tables_relAtIn (fp : ℕ) (rd : Reader)
    (hL : MemL rd [(fp + fs "exponent_tables", expTbl1), (fp + fs "exponent_tables" + 34, expTbl2)]) :
    RelAtInB S coreProgram fs cert rd (RegionL [])
      (RegionL [(fp + fs "exponent_tables", expTbl1), (fp + fs "exponent_tables" + 34, expTbl2)]) fp
      (fs "exponent_tables" + [34, 34].sum + 0) "exponent_tables" []
      [ofK (gpow (fp + fs "exponent_tables")), ofK (gpow (fp + fs "exponent_tables" + 34))] := by
  set b := fp + fs "exponent_tables" with hb
  obtain ⟨p1, p2, p3, p4, p5⟩ := etPre_parts
  have ht := expTables_of_memL (b := b) hL (by simp) (by simp)
  set σ := etVal (ofK (gpow b)) (ofK (gpow (b + 34)))
  have hH := etS_holds (S := S) (C := fun _ _ _ => True) ht
  have hwf : Stmt.wfList coreProgram etBody = true := by
    have := coreProgram_wf Data.core2 (List.mem_of_find?_eq_some find_exponent_tables)
    rwa [core2_body] at this
  have hw := walk_straight σ [.n 70, .n 71] etPre p1
  rw [← etBody_eq] at hw
  have hsat := walkB_sat etBody hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ etPre p1
  rw [p2] at e1 e2
  rw [p3] at e3
  rw [p4] at e4
  have hal : allocs σ (etPre.flatMap (slEvs σ)) = [34, 34] := by rw [e2]; rfl
  have hown : ∀ i, RegionL [(b, expTbl1), (b + 34, expTbl2)] i →
      ownData cert fp (fp + fs "exponent_tables") "exponent_tables"
        (allocs σ (etPre.flatMap (slEvs σ))) (etPre.flatMap (slEvs σ)) i := fun i hi => by
    rw [hal]
    refine Or.inl ?_
    obtain ⟨q, hq, h1, h2⟩ := hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨(34, b), by simp [bases, hb], h1, by simpa [expTbl1] using h2⟩
    · exact ⟨(34, b + 34), by simp [bases, hb], h1, by simpa [expTbl2] using h2⟩
  have := relAtInB_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL [])
    (D := RegionL [(b, expTbl1), (b + 34, expTbl2)]) (Dk := fun _ => False) (N := 0) (fp := fp)
    (σ := σ) (rd := rd) (args := []) (rets := [ofK (gpow b), ofK (gpow (b + 34))])
    coreProgram_wf find_exponent_tables (Or.inl exponent_tables_not_loop)
    (by rw [show Fn.params Data.core2 = [] from rfl]; rfl) (by rw [core2_body]; exact hw)
    (by simp only [σ, etVal, List.map_cons, List.map_nil]; b1_look)
    (fun e he => (hsat.1 e he).1) (by rw [e1, hal]; simp only [σ, etVal, List.map_cons, List.map_nil, bases]; b1_look; rfl)
    (by rw [e3]; simp) (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) ?_ (fun i hi => Or.inl (hown i hi))
  · rwa [hal] at this
  · intro A hA
    rw [LeanVM.Guest.B1.loadAddrs_straight σ etPre p1, p5, List.map_append, List.mem_append] at hA
    rcases hA with hA | hA <;> simp only [List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hA <;> obtain ⟨j, hj, rfl⟩ := hA
    · refine ⟨b + j, ?_, Or.inl (hown _ ⟨(b, expTbl1), by simp, by omega, by simp [expTbl1]; omega⟩)⟩
      simp only [σ, etVal]; b1_look; exact addr_ofK b j
    · refine ⟨b + 34 + j, ?_,
        Or.inl (hown _ ⟨(b + 34, expTbl2), by simp, by omega, by simp [expTbl2]; omega⟩)⟩
      simp only [σ, etVal]; b1_look; exact addr_ofK (b + 34) j

/-- **`exponent_tables`, placed**: at every `fp` its tables in its two `HeapBuf`s, returned, its
tree its frame and the tables. -/
theorem exponentS_tables_completeAt (κ : ℕ) :
    CompleteAtBS S fs cert κ "exponent_tables" [] [] ExpOut (fs "exponent_tables" + 68) := by
  intro fp
  refine ⟨_, [], _, _, ⟨fp + fs "exponent_tables", rfl, rfl⟩, fun q hq => ?_, ?_, le_of_eq rfl,
    fun rd _ hL => exponentS_tables_relAtIn fp rd (by simpa using hL)⟩
  · simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [expTbl1, expTbl2] <;> omega
  · simp only [List.append_nil, DisjL, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    left; simp [expTbl1]

end
end LeanVM.Guest.B1.Main
