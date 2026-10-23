/-
  LeanVM.Guest.B1.Main.MainHonestFit

  `main`'s honest run fits its buffers and its bounds: each honest buffer has its `HeapBuf`'s
  size, the oracle's counts are within `main`'s bounds under the deployed limits, and the running
  counts end at the coverage table's size.
-/

module

public import LeanVM.Guest.B1.Main.MainGoals

/-!
# `main`'s honest run fits

`hOwn_lengths`: the honest buffers' lengths are `mSizes`, for a statement of the bytecode's
shape (`Nat.log2 bytecode.length = 23`) and children whose fresh claims are at points of `23`
coordinates; `hOwn_fit` the `Forall₂` `main_relAtIn` takes. `hData_bounds`: `MainBounds` under
`Limits`. `hW_total`: the running count after the last child is the coverage table's size.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct claimCells cellsOfBytes plan)
open LeanVM.Guest.Value.Keccak (cellsBytes)

@[expose] public section

/-- **The children's fresh claims are at points of `23` coordinates**, as the deferring
verifier's bus point is. -/
def FreshShaped (w : NodeWitness) : Prop := ∀ c ∈ w.children, c.fresh.bytecodePoint.length = 23

theorem forall₂_of_map_length : ∀ (l : List (List E)) (ss : List ℕ), l.map List.length = ss →
    List.Forall₂ (fun c s => c.length ≤ s) l ss
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, s :: ss, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1.le (forall₂_of_map_length l ss h.2)

theorem length_daCells (c : DaClaim) : (daCells c).length = 4 := by
  simp [daCells, B1.Digest.digestCells]

theorem length_claimCells (r p : BitVec 128) (m : BitVec 256) : (claimCells r p m).length = 4 := by
  simp [claimCells, cellsOfBytes, claimBytes, bytes16, LeanXmss.bytesLE]

theorem length_flatMap_const {α : Type} (l : List α) (f : α → List E) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

theorem length_hCover : (hCover s w).length = (hData seed s w).T := by
  simp only [hCover, hData, MainData.T, MainData.X, MainData.Y, MainData.S, List.length_append,
    List.length_map, List.length_range]

/-- **The honest buffers have their sizes.** -/
theorem hOwn_lengths (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRel bytecode seed s w)
    (hf : FreshShaped w) : (hOwn seed s w).map List.length = mSizes (hData seed s w) := by
  obtain ⟨hsd, hch, -, -, -, -⟩ := hr
  simp only [hOwn, mSizes, List.map_cons, List.map_nil, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [length_flatMap_const _ _ 4 fun c _ => length_daCells c]
    simp [hData, MainData.S]
  · rw [length_flatMap_const _ (fun c : XmssClaim => claimCells c.1.root c.1.parameter c.2) 4
      fun c _ => length_claimCells _ _ _]
    simp [hData, MainData.X]
  · rw [length_flatMap_const _ (fun c : SphincsClaim => claimCells c.1.root c.1.parameter c.2) 4
      fun c _ => length_claimCells _ _ _]
    simp [hData, MainData.Y]
  · simp [B1.Digest.digestCells]
  · exact length_hCover
  · simp
  · rw [length_flatMap_const _ _ 2 fun c _ => by simp [B1.Digest.digestCells]]
    simp [hData]
  · rw [length_flatMap_const _ _ 24 fun c hc => by simp [fixedCells, hf c hc]]
    simp [hData]
  · rw [length_flatMap_const _ _ 24 fun c hc => by
      simp [DeferredClaim.cells, Eq.trans (hch c hc).1 hlog]]
    simp [hData]
  · simp [hData]
  · simp [DeferredClaim.cells, Eq.trans hsd hlog]

theorem hOwn_fit (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRel bytecode seed s w)
    (hf : FreshShaped w) :
    List.Forall₂ (fun c s => c.length ≤ s) (hOwn seed s w) (mSizes (hData seed s w)) :=
  forall₂_of_map_length _ _ (hOwn_lengths hlog hr hf)

/-! ## The counts -/

theorem length_made {α : Type} (R : List α) (Cs : List (List α)) :
    (made R Cs).length = R.length + (Cs.map List.length).sum := by
  simp [made, List.length_flatten]

/-- The running count before child `c`: the raw claims, then the first `c` children's. -/
theorem hW_eq (c : ℕ) : hW s w c = (hRawX s w).length + (hRawS s w).length + (hRawD s w).length +
    (((w.children.take c).map (·.statement.claims.xmss.length)).sum +
      ((w.children.take c).map (·.statement.claims.sphincs.length)).sum +
      ((w.children.take c).map (·.statement.claims.da.length)).sum) := by
  induction c with
  | zero => simp [hW]
  | succ c ih =>
    rw [hW, ih, List.take_add_one]
    simp only [hEx, hEs, hEd, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    rcases w.children[c]? with _ | ch
    · simp
    · simp; ring

theorem length_raw {α W : Type} (l : List (α × W)) : (l.map (·.1)).length = l.length := by simp

/-- **After the last child, the running count is the coverage table's size.** -/
theorem hW_total (hl : Limits bytecode s w) : hW s w w.children.length = coverage s w := by
  rw [hW_eq, List.take_length, coverage_made hl, length_made, length_made, length_made]
  simp only [hRawX, hRawS, hRawD, length_raw, List.map_map]
  simp only [Function.comp_def]
  omega

theorem sum_le_16 {α : Type} (l : List α) (f : α → ℕ) (h : ∀ a ∈ l, f a ≤ 16) :
    (l.map f).sum ≤ l.length * 16 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    have := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    nlinarith

/-- **The DA region has at most `257` slots**: one direct claim and `16` per child. -/
theorem da_slots (hl : Limits bytecode s w) : (s.claims.da ++ (dPlan s w).dups).length ≤ 257 := by
  rw [dPlan, plan_table_length _ _ _ (dPlan_held hl), length_made, length_raw, List.map_map]
  have h1 := hl.directDa
  have h2 := sum_le_16 w.children (List.length ∘ (·.statement.claims.da)) fun c hc => hl.daRoots.2 c hc
  have h3 := hl.children
  have : w.children.length * 16 ≤ 256 := by omega
  omega

theorem raw_le_table {α W : Type} [BEq α] [LawfulBEq α] (D : List α) (R : List (α × W))
    (Cs : List (List α)) (hc : ∀ x, D.count x ≤ (made (R.map (·.1)) Cs).count x) :
    R.length ≤ (D ++ (plan D (R.map (·.1)) Cs).dups).length := by
  rw [plan_table_length _ _ _ hc, length_made, length_raw]; omega

/-- **`main`'s honest counts are within its bounds**, under the deployed limits. -/
theorem hData_bounds (hl : Limits bytecode s w) (fs : String → ℕ) (fp : ℕ) :
    MainBounds ((hData seed s w).toIn fs fp) := by
  have hc := hl.coverage
  rw [coverage_eq] at hc
  have hx : (direct s.claims.xmss w.xmss).length ≤ (s.claims.xmss ++ (xPlan s w).dups).length :=
    raw_le_table s.claims.xmss (direct s.claims.xmss w.xmss) _ (xPlan_held hl)
  have hs : (direct s.claims.sphincs w.sphincs).length ≤
      (s.claims.sphincs ++ (sPlan s w).dups).length :=
    raw_le_table s.claims.sphincs (direct s.claims.sphincs w.sphincs) _ (sPlan_held hl)
  have hd := da_slots hl
  simp only [List.length_append] at hc hx hs hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hl.children, hl.directDa, hl.daRoots.1, ?_, ?_, ?_, ?_⟩
  all_goals simp only [MainData.toIn, hData, MainIn.total, hRawX, hRawS]
  all_goals first | exact Nat.pos_iff_ne_zero.mp hl.nonempty | omega

/-! ## `main`'s words on an honest memory -/

theorem mem_bufL_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)} (hlen : own.length = sizes.length)
    {i : ℕ} (hi : i < sizes.length) :
    ((bases b sizes).getD i 0, own.getD i []) ∈ bufL b sizes own := by
  have h1 : i < (bases b sizes).length := by rw [length_bases]; exact hi
  have h2 : i < own.length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  have h3 : i < ((bases b sizes).zip own).length := by simp [List.length_zip]; omega
  have := List.getElem_mem h3
  rwa [List.getElem_zip] at this

theorem cellsBytes_digestCells (x y : Digest) :
    cellsBytes (B1.Digest.digestCells x ++ B1.Digest.digestCells y) = digestBytes x ++ digestBytes y := by
  rw [digestBytes_eq_cells, digestBytes_eq_cells]
  simp [cellsBytes, B1.Digest.digestCells]

/-- **`main`'s header-free reads hold on a memory holding its honest buffers.** -/
theorem hMainMem (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRel bytecode seed s w)
    (hf : FreshShaped w) (hl : Limits bytecode s w) (fs : String → ℕ) (fp : ℕ) (rd : Reader)
    (hM : B1.Main.MemL rd (bufL (fp + fs "main") (mSizes (hData seed s w)) (hOwn seed s w)))
    (h0 : LoadHolds rd 1 0 (digestScalars (statementDigest seed s)).1)
    (h1 : LoadHolds rd gen 0 (digestScalars (statementDigest seed s)).2) :
    MainMem rd ((hData seed s w).toIn fs fp) := by
  have hlen : (hOwn seed s w).length = (mSizes (hData seed s w)).length := by
    rw [← hOwn_lengths hlog hr hf, List.length_map]
  have hR : ∀ i < 11, ReadsAt rd (gen ^ ((mPos (hData seed s w) (fp + fs "main")).getD i 0))
      ((hOwn seed s w).getD i []) := fun i hi =>
    by rw [gen_pow_eq_ofK]; exact hM _ (mem_bufL_getD hlen (by simp [mSizes]; omega))
  obtain ⟨-, -, -, -, -, hz⟩ := hr
  refine ⟨?_, hR 5 (by omega), ?_, ?_, ?_, h0, h1⟩
  · have := hR 3 (by omega)
    simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero, signersDigest] at this
    show ReadsAt rd (gen ^ ((mPos (hData seed s w) (fp + fs "main")).getD 3 0))
      (B1.Digest.digestCells (keccak256 (cellsBytes (B1.Digest.digestCells (xmssListDigest s.claims.xmss) ++
        B1.Digest.digestCells (sphincsListDigest s.claims.sphincs)))))
    rw [cellsBytes_digestCells]
    exact this
  · have := hR 9 (by omega) 0 (by simp [hOwn])
    simpa [hOwn, MainData.toIn, hData, hW] using this
  · have := hR 9 (by omega) w.children.length (by simp [hOwn])
    simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero, List.getElem_map,
      List.getElem_range] at this
    rw [hW_total hl, coverage_eq] at this
    show LoadHolds rd (gen ^ ((mPos (hData seed s w) (fp + fs "main")).getD 9 0) * gen ^ w.children.length) 0
      (gen ^ (s.claims.xmss.length + (xPlan s w).dups.length + (s.claims.sphincs.length +
        (sPlan s w).dups.length) + (s.claims.da.length + (dPlan s w).dups.length)))
    rw [loadHolds_mul_gen_pow, Nat.add_zero]
    simp only [List.length_append] at this
    exact this
  · intro hnc
    have hc : w.children = [] := List.eq_nil_of_length_eq_zero hnc
    simp only [hc, ↓reduceIte] at hz
    have hz' : s.defer.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0 := hz
    rw [hlog] at hz'
    have := hR 10 (by omega)
    simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero, DeferredClaim.cells, hz'] at this
    exact this
end
end LeanVM.Guest.B1.Main
