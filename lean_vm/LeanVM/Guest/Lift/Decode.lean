/-
  LeanVM.Guest.Lift.Decode

  `decode_query_bits__L{d}` complete in the placed form `open_stacked`'s squeeze loop takes
  (`OsDecodeAtD`), on the region its loads read: its frame run holds the word's bits, the caller's
  words its positions and pointers.
-/

module

public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.B1.Place.OsCallees
public import LeanVM.Guest.B1.Bits.QueryBits

/-!
# `decode_query_bits`, placed

**The form** (`OsDecodeRegAtD`): B1-b's `OsDecodeAtD` (`B1/Place/OsCallees.lean`) with the premise
that the `192 / d` positions at `pos` and pointers at `ptrs` lie in the caller's words
(`RegPtrs (dqSpec d)`, as `CompleteRelRegD` takes of the pure callees). At every frame pointer `fp`,
on every memory where the caller's words hold the decoded positions and the pointers
`g^(fp + cert name (.n 3))·g^(j·d)` into the run, a tree of `fs name` words holds whose data is the
run of the word's 192 bits at its certificate cell (`dqRunL`).

**The lift** (`osDecodeRegAtD_of`): the body is a straight line of atoms ending in `ret []`
(`bodyAtoms`), its one `frameAddr` the run `.n 3 .. .n 194` at `.n 195`, no `HeapBuf`, its loads
from `pos` (`.n 1`) and `ptrs` (`.n 2`) at offsets below `192 / d`, and it loads `.n 195` from
`ptrs[0]` (`decodeShapeB`, a kernel check). The memory holding the run makes the meaning true
(`FrameBits192` at `g^(fp + cert name (.n 3))`), so the relation holds (B1's
`decode_query_bits_all_holds`); the load of `.n 195` from `ptrs[0]` makes the `frameAddr` the run's
address in the frame, so `relAtIn_of_walk` places the walk. The run fits the frame by the
certificates' `Lift.RunsFit`.

`osDecodeRegAtD_holds`: every deployed depth, `14 .. 26`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **`decode_query_bits__L{d}`, placed, on the region it loads**: `OsDecodeAtD` for positions and
pointers in the caller's words. -/
def OsDecodeRegAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) :
    Prop :=
  ∀ (w pos ptrs : E) (Lin : Layout) (fp : ℕ),
    RegPtrs [(1, 192 / d), (2, 192 / d)] [w, pos, ptrs] (RegionL Lin) →
    (∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (gpow (fp + cert name (.n 3))) * gen ^ (j * d))) →
    ∃ Lown : Layout, Within (dqRunL cert name fp w ++ Lown) fp (fs name) ∧
      DisjL (dqRunL cert name fp w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (dqRunL cert name fp w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (dqRunL cert name fp w)) fp
          (fs name) name [w, pos, ptrs] []

/-! ## The body's shape -/

/-- The frame run of `decode_query_bits`' bits: `.n 3 .. .n 194`. -/
def dqRunV : List V := .n 3 :: (List.range 191).map fun i => V.n (i + 4)

/-- Its loads: `192 / d` words from `pos` (`.n 1`) and from `ptrs` (`.n 2`). -/
def dqSpec (d : ℕ) : List (ℕ × ℕ) := [(1, 192 / d), (2, 192 / d)]

/-- An atom of `decode_query_bits`' body: the `frameAddr` of its run at `.n 195`, no `HeapBuf`,
its loads as `dqSpec`. -/
def dqAtomOk (d : ℕ) : Atom → Bool
  | .frameAddr p run => decide (p = .n 195) && decide (run = dqRunV)
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | a => specLoad (dqSpec d) a

/-- The atoms of a straight-line body ending in `ret []`. -/
def bodyAtoms : List Stmt → Option (List Atom)
  | [] => none
  | .atom a :: ss => (bodyAtoms ss).map (a :: ·)
  | .ret vs :: ss => if vs.isEmpty && ss.isEmpty then some [] else none
  | _ :: _ => none

/-- **The kernel's check of `decode_query_bits__L{d}`**: its parameters `.n 0, .n 1, .n 2`, its
body a straight line of `dqAtomOk` atoms ending in `ret []`, with the run's `frameAddr` and the
load of `.n 195` from `ptrs[0]`; at least one group. -/
noncomputable def decodeShapeB (name : String) (d : ℕ) : Bool :=
  decide (0 < 192 / d) &&
  match coreProgram.find? name with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      match bodyAtoms fn.body with
      | some as => as.all (dqAtomOk d) &&
          as.any (fun a => decide (a = .frameAddr (.n 195) dqRunV)) &&
          as.any (fun a => decide (a = .load (.n 195) (.n 2) 0))
      | none => false
  | none => false

theorem bodyAtoms_eq : ∀ {ss : List Stmt} {as : List Atom}, bodyAtoms ss = some as →
    ss = as.map Stmt.atom ++ [.ret []]
  | [], _, h => by simp [bodyAtoms] at h
  | .atom a :: ss, as, h => by
    cases hb : bodyAtoms ss with
    | none => simp [bodyAtoms, hb] at h
    | some as' =>
      simp [bodyAtoms, hb] at h
      subst h
      rw [bodyAtoms_eq hb]
      rfl
  | .ret vs :: ss, as, h => by
    simp only [bodyAtoms] at h
    split at h
    · rename_i hv
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hv
      obtain ⟨rfl, rfl⟩ := hv
      cases h
      rfl
    · cases h
  | .ite .. :: _, _, h => by simp [bodyAtoms] at h
  | .match_ .. :: _, _, h => by simp [bodyAtoms] at h
  | .call .. :: _, _, h => by simp [bodyAtoms] at h
  | .callIf .. :: _, _, h => by simp [bodyAtoms] at h
  | .dispatch .. :: _, _, h => by simp [bodyAtoms] at h

theorem blockAtoms_atoms : ∀ as : List Atom, Lift.blockAtoms (as.map Stmt.atom ++ [.ret []]) = as
  | [] => by simp [Lift.blockAtoms, Lift.stmtAtoms]
  | a :: as => by
    rw [List.map_cons, List.cons_append, Lift.blockAtoms, blockAtoms_atoms as]
    rfl

theorem walk_atoms (σ : Val) (as : List Atom) :
    walk σ (as.map Stmt.atom ++ [.ret []]) = .ret (as.map Ev.atom) [] := by
  rw [walk_straight σ [] (as.map Stmt.atom) (by simp [Stmt.straight])]
  congr 1
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.flatMap_cons, ih, slEvs, List.singleton_append]

structure DecodeShape (name : String) (d : ℕ) (fn : Fn) (as : List Atom) : Prop where
  pos : 0 < 192 / d
  find : coreProgram.find? name = some fn
  params : fn.params = [.n 0, .n 1, .n 2]
  body : fn.body = as.map Stmt.atom ++ [.ret []]
  atoms : ∀ a ∈ as, dqAtomOk d a = true
  run : Atom.frameAddr (.n 195) dqRunV ∈ as
  load : Atom.load (.n 195) (.n 2) 0 ∈ as

theorem decodeShape_of {name : String} {d : ℕ} (h : decodeShapeB name d = true) :
    ∃ fn as, DecodeShape name d fn as := by
  unfold decodeShapeB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h⟩ := h
  split at h
  · rename_i fn hf
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i as has
      simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h2
      obtain ⟨⟨hall, ⟨a1, ha1, rfl⟩⟩, ⟨a2, ha2, rfl⟩⟩ := h2
      exact ⟨fn, as, of_decide_eq_true h0, hf, of_decide_eq_true h1, bodyAtoms_eq has, hall, ha1,
        ha2⟩
    · cases h2
  · cases h

theorem dq_alloc {d : ℕ} {σ : Val} {a : Atom} (h : dqAtomOk d a = true) :
    Ev.alloc? σ (.atom a) = none ∧ Ev.allocDst? (.atom a) = none := by
  cases a <;> first | exact ⟨rfl, rfl⟩ | skip
  rename_i hh
  cases hh <;> first | exact ⟨rfl, rfl⟩ | simp [dqAtomOk] at h

theorem dq_specLoad {d : ℕ} {a : Atom} (h : dqAtomOk d a = true) : specLoad (dqSpec d) a = true := by
  cases a <;> first | rfl | exact h

theorem dq_addr {d : ℕ} {as : List Atom} (h : ∀ a ∈ as, dqAtomOk d a = true) :
    ∀ q ∈ addrs (as.map Ev.atom), q = (.n 195, .n 3) := by
  intro q hq
  obtain ⟨e, he, hq⟩ := List.mem_filterMap.mp hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  have hok := h a ha
  cases a with
  | frameAddr p run =>
    simp only [dqAtomOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    simp only [dqRunV, Ev.addr?, Option.some.injEq] at hq
    exact hq.symm
  | _ => simp [Ev.addr?] at hq

/-! ## The lift -/

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`decode_query_bits__L{d}` placed on its region**, from its body's shape, its meaning and the
certificates' frame runs fitting their frames. -/
theorem osDecodeRegAtD_of {name : String} {d : ℕ} (hfit : Lift.RunsFit fs cert)
    (hshape : decodeShapeB name d = true) (hiff : decode_query_bits_Spec name d) (k : ℕ) :
    OsDecodeRegAtD fs cert k d name := by
  obtain ⟨fn, as, hS⟩ := decodeShape_of hshape
  intro w pos ptrs Lin fp hreg hpre
  have hc3 : cert name (.n 3) + 192 ≤ fs name := by
    have h := hfit name fn hS.find (.n 195) (.n 3) ((List.range 191).map fun i => V.n (i + 4))
      (by rw [hS.body, blockAtoms_atoms]; exact hS.run)
    simpa using h
  refine ⟨[], fun q hq => ?_, ?_, fun rd hlow hL => ?_⟩
  · simp only [dqRunL, List.append_nil, List.mem_singleton] at hq
    subst hq
    simp only [List.length_map, List.length_range]
    omega
  · simp [DisjL, dqRunL]
  · rw [List.append_nil] at hL
    obtain ⟨hR, hLin⟩ := Main.memL_append.mp hL
    -- the meaning, at the run's address
    have hmean : MeaningDecodeQueryBits d rd [w, pos, ptrs] [] := by
      refine ⟨rfl, ofK (gpow (fp + cert name (.n 3))), ⟨(isInK_iff _).mpr ⟨_, rfl⟩,
        fun j hj v hv => ?_⟩, hpre rd hlow hLin⟩
      have h := (hR _ (List.mem_singleton_self _) j (by simpa using hj)).2
      rw [hv, Option.some.injEq] at h
      rw [h]
      simp
    obtain ⟨t, hn, hv, -⟩ := Program.Rel.tree coreProgram_wf ((hiff rd _ _).mpr hmean)
    cases t with
    | phantom => exact hv.elim
    | node f σ bufs kids =>
      simp only [Tree.name] at hn
      subst f
      obtain ⟨fn', hf', hp, es, vs, hw, hr, hes, -⟩ := hv
      rw [hS.find, Option.some.injEq] at hf'
      subst hf'
      have hw' := hw
      rw [hS.body, walk_atoms, Out.ret.injEq] at hw'
      obtain ⟨rfl, rfl⟩ := hw'
      have hp' := hp
      rw [hS.params] at hp'
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp'
      obtain ⟨-, h1, h2, -⟩ := hp'
      have hcalls : calls (as.map Ev.atom) = [] := by
        rw [calls, List.filterMap_map]
        exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
      have hal : allocs σ (as.map Ev.atom) = [] := by
        rw [allocs, List.filterMap_map]
        exact List.filterMap_eq_nil_iff.mpr fun a ha => (dq_alloc (σ := σ) (hS.atoms a ha)).1
      have hald : allocDsts (as.map Ev.atom) = [] := by
        rw [allocDsts, List.filterMap_map]
        exact List.filterMap_eq_nil_iff.mpr fun a ha => (dq_alloc (σ := σ) (hS.atoms a ha)).2
      -- the `frameAddr` pointer: the load of `.n 195` from `ptrs[0]`
      have h195 : σ (.n 195) = ofK (gpow (fp + cert name (.n 3))) := by
        have hl := (hes _ (List.mem_map_of_mem hS.load)).2
        have hl' := ((hpre rd hlow hLin 0 hS.pos).2).2
        rw [h2] at hl
        rw [hl, Option.some.injEq] at hl'
        rw [hl']
        simp
      have hrun : ((V.n 3), 192) ∈ runs (as.map Ev.atom) :=
        List.mem_filterMap.mpr ⟨_, List.mem_map_of_mem hS.run, by simp [Ev.run?, dqRunV]⟩
      have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
        (D := RegionL (dqRunL cert name fp w)) (Dk := fun _ => False) (N := 0) (fp := fp)
        coreProgram_wf hS.find (Or.inr hcalls) hp hw hr hes (by rw [hald, hal]; rfl)
        (fun q hq => by rw [dq_addr hS.atoms q hq]; exact h195)
        (by rw [hcalls]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_) (fun i hi => ?_)
      · simpa only [hal, List.sum_nil, Nat.add_zero] using h
      · have hall : ∀ e ∈ as.map Ev.atom, Lift.EvLeafOk (specLoad (dqSpec d)) e := by
          intro e he
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
          exact dq_specLoad (hS.atoms a ha)
        obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
        obtain ⟨i, hi, hreg'⟩ := hreg q hq off hoff
        refine ⟨i, ?_, Or.inr (Or.inl hreg')⟩
        rw [← hi]
        simp only [dqSpec, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl
        · show (σ (.n 1)).limb 0 * Parameters.gpow off = pos.limb 0 * Parameters.gpow off
          rw [h1]
        · show (σ (.n 2)).limb 0 * Parameters.gpow off = ptrs.limb 0 * Parameters.gpow off
          rw [h2]
      · obtain ⟨q, hq, hq1, hq2⟩ := hi
        simp only [dqRunL, List.mem_singleton] at hq
        subst hq
        simp only [List.length_map, List.length_range] at hq2
        exact Or.inl (Or.inr ⟨_, hrun, hq1, hq2⟩)

/-! ## The deployed depths -/

set_option maxRecDepth 100000 in
theorem decode_shape : (decodeQueryBitsNames.all fun p => decodeShapeB p.1 p.2) = true := by
  decide +kernel

/-- **`decode_query_bits__L{d}` is complete placed on its region**, at every deployed depth, for
certificates whose frame runs fit their frames. -/
theorem osDecodeRegAtD_holds (hfit : Lift.RunsFit fs cert) (k : ℕ) :
    ∀ p ∈ decodeQueryBitsNames, OsDecodeRegAtD fs cert k p.2 p.1 := fun p hp =>
  osDecodeRegAtD_of hfit (List.all_eq_true.mp decode_shape p hp) (decode_query_bits_all_holds p hp) k

end
end LeanVM.Guest.B1
