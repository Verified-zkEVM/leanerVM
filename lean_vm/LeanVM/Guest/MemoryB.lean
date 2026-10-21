/-
  LeanVM.Guest.MemoryB

  The honest memory of an evaluation (`Memory.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.PlacedB

/-!
# The honest memory under any `BLAKE2S` semantics

`Memory.lean`'s memory (`honest`, `honestInsts`, `frameWrites`) is built from a tree, not from
the semantics; what mentions the semantics is the evaluation's validity. Here `Inst.GoodB`,
`HonestB` and `HonestAtB` are `Memory.lean`'s with `S : BlakeSem` a parameter, and their lemmas
(`HonestB.consistent`, `HonestB.read_C`, `HonestB.read_hdr`, `HonestB.valid_image`,
`HonestB.publicBoundary`, `HonestAtB.nodeAt`, `honestAtB_of_read`, …) are proved as there.

* `honestB_deployed`, `honestAtB_deployed`, `inst_goodB_deployed`: at `blakeDeployed`, they are
  `Memory.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

/-! ## Validity of the instances -/

section Valid

variable {P : Core.Program} {rd : Reader} {fs : String → ℕ} {lp : String → Bool}
  {H : Inst → ℕ → E × E}

variable (S) in
/-- An instance that runs is a valid tree; the others are phantoms. -/
def Inst.GoodB (P : Core.Program) (rd : Reader) (I : Inst) : Prop :=
  (∃ args rets, I.t.ValidB S P rd args rets) ∨ ∃ f σ, I.t = .phantom f σ

mutual
/-- Every instance of a valid tree is valid or a phantom. -/
theorem instsB_good : ∀ (t : Tree) (fp : ℕ) (hdr : E × E) {args rets : List E},
    t.ValidB S P rd args rets → ∀ I ∈ t.insts fs lp H fp hdr, I.GoodB S P rd
  | .node f σ bufs kids, fp, hdr, args, rets, hv, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact Or.inl ⟨args, rets, hv⟩
      · obtain ⟨_, _, _, es, _, _, _, _, hk⟩ := hv
        exact instsKidsB_good kids σ (calls es) _ 0 _ hk I hI
  | .phantom .., _, _, _, _, hv, _, _ => hv.elim

/-- `instsB_good` for the callees. -/
theorem instsKidsB_good : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (I : Inst) (j : ℕ)
    (ps : List ℕ), Tree.KidsValidB S P rd σ cs ks → ∀ J ∈ Tree.instsKids fs lp H I j ps ks, J.GoodB S P rd
  | [], _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, J, hJ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨_, hc, hks⟩, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact instsB_good k _ _ hc J hJ
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          rw [insts_phantom, List.mem_singleton] at hJ
          exact Or.inr ⟨f, σ', by rw [hJ]⟩
      · exact instsKidsB_good ks σ cs I (j + 1) ps hks J hJ
  | _ :: _, _, [], _, _, _ :: _, h, _, _ => h.elim
end

end Valid

/-! ## Equations -/

/-- **The equations are consistent** when the evaluation is valid on a memory holding their
addresses. -/
theorem Tree.ValidB.eqns_consistent {P : Core.Program} {κ : ℕ} (hκ : κ < 64) {M : MemImage κ}
    {T : Tree} {args rets : List E} (hv : T.ValidB S P M.read args rets)
    (ha : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ κ), q.1 = gpow i) : Consistent (T.eqns P) :=
  consistent_of_read fun q hq => hv.eqns_read hκ T q hq (ha q hq)

/-! ## The honest memory -/

section Honest

variable (P : Core.Program) (fs : String → ℕ) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
  (hdr : E × E) (T : Tree)

variable (S) in
/-- What the honest memory needs. -/
structure HonestB (rd : Reader) (args rets : List E) : Prop where
  /-- The evaluation, on some reader. -/
  valid : T.ValidB S P rd args rets
  /-- At most `2^32` words are allocated. -/
  size : T.total fs ≤ 2 ^ 32
  /-- The cells fit their frames and agree. -/
  cells : CellsOk fs C (honestInsts P fs H hdr T)
  /-- The equations name addresses of the memory. -/
  addr : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = gpow i
  /-- The equations agree among themselves. -/
  eqns : Consistent (T.eqns P)
  /-- The equations agree with the frames where they meet. -/
  cross : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), ∀ b ∈ T.eqns P, a.1 = b.1 → a.2 = b.2

variable (S) in
/-- What the honest memory of a placed tree needs: `HonestB`, every `HeapBuf` that of its path,
and the tree placed from `main`'s frame at word `0` (`Tree.Placed`, the certificate `cert` placing
the `frameAddr`s), so that every `HeapBuf` pointer is its instance's base and every `frameAddr`
the address of its run (`HonestAtB.nodeAt`). -/
structure HonestAtB (cert : String → V → ℕ) (rd : Reader) (args rets : List E) : Prop
    extends HonestB S P fs H C hdr T rd args rets where
  /-- The `HeapBuf`s are those of the paths. -/
  bufsOk : T.BufsOk P
  /-- The tree is placed from word `0`. -/
  placed : T.Placed P fs cert 0

variable {P fs H C hdr T} {rd : Reader} {args rets : List E}

theorem HonestB.logMem_le (h : HonestB S P fs H C hdr T rd args rets) :
    logMem (T.total fs) ≤ maxLogMem :=
  logMem_le_maxLogMem h.size

theorem HonestB.lt_64 (h : HonestB S P fs H C hdr T rd args rets) : logMem (T.total fs) < 64 := by
  have := h.logMem_le; unfold maxLogMem at this; omega

/-- **Write-once consistency** of the honest memory's writes. -/
theorem HonestB.consistent (h : HonestB S P fs H C hdr T rd args rets) :
    Consistent (frameWrites C (honestInsts P fs H hdr T) ++ T.eqns P) :=
  (frameWrites_consistent (insts_pairwise T 0 hdr) h.cells fun I hI => by
    have := honest_within hI (by have := h.cells.two_le I hI; omega)
    have := h.size
    omega).append h.eqns h.cross

/-- **Every frame cell reads back**: header and cells, at `fp · g^o`. -/
theorem HonestB.read_cell (h : HonestB S P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) {q : ℕ × E} (hq : q ∈ I.cells C) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow q.1) = some q.2 := by
  have hlt := h.cells.cell_lt hI hq
  have hw := honest_within hI (by omega)
  have hle := le_two_pow_logMem (T.total fs)
  rw [← pow_add]
  exact image_read h.lt_64 h.consistent (q := (gpow (I.fp + q.1), q.2))
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨q, hq, rfl⟩⟩))
    ⟨⟨I.fp + q.1, by omega⟩, rfl⟩

/-- The header: `fp[0]`, `fp[1]`. -/
theorem HonestB.read_hdr (h : HonestB S P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow 0) = some I.hdr.1 ∧
      (honest P fs H C hdr T).read (gpow I.fp * gpow 1) = some I.hdr.2 :=
  ⟨h.read_cell hI (q := (0, I.hdr.1)) List.mem_cons_self,
    h.read_cell hI (q := (1, I.hdr.2)) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- A cell of `C`. -/
theorem HonestB.read_C (h : HonestB S P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) {o : ℕ} {w : E} (hq : (o, w) ∈ C I) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow o) = some w :=
  h.read_cell hI (q := (o, w)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))

/-- Every memory equation reads back. -/
theorem HonestB.read_eqn (h : HonestB S P fs H C hdr T rd args rets) {q : Write}
    (hq : q ∈ T.eqns P) : (honest P fs H C hdr T).read q.1 = some q.2 :=
  image_read h.lt_64 h.consistent (List.mem_append_right _ hq) (h.addr q hq)

/-- **The evaluation is valid on the honest memory.** -/
theorem HonestB.valid_image (h : HonestB S P fs H C hdr T rd args rets) :
    T.ValidB S P (honest P fs H C hdr T).read args rets :=
  h.valid.transfer T fun _ hq => h.read_eqn hq

/-- **Every instance is valid on the honest memory**, or a phantom. -/
theorem HonestB.inst_good (h : HonestB S P fs H C hdr T rd args rets) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) : I.GoodB S P (honest P fs H C hdr T).read :=
  instsB_good T 0 hdr h.valid_image I hI

/-- **The public boundary**: with the public input as `main`'s header, the honest memory holds
it in words `0`, `1`, and has between `2^16` and `2^32` words. -/
theorem HonestB.publicBoundary {input : PublicInput} {prog : Semantics.Program}
    (h : HonestB S P fs H C (input.word0, input.word1) T rd args rets) :
    HasPublicBoundary input
      (⟨logMem (T.total fs), honest P fs H C (input.word0, input.word1) T, 0⟩ : Trace prog) := by
  obtain ⟨I, hI, -, hfp, hh⟩ := root_inst (fs := fs) (H := H) (hdr := (input.word0, input.word1))
    (T := T)
  obtain ⟨h0, h1⟩ := h.read_hdr hI
  rw [hfp, hh, gpow, pow_zero, one_mul] at h0 h1
  exact ⟨minLogMem_le_logMem _, h.logMem_le, h0, h1⟩

/-- A word nothing writes reads `0`, as the Rust runner reads an unwritten cell. -/
theorem HonestB.read_unwritten (h : HonestB S P fs H C hdr T rd args rets)
    (i : Fin (2 ^ logMem (T.total fs)))
    (hn : ∀ q ∈ frameWrites C (honestInsts P fs H hdr T) ++ T.eqns P, q.1 ≠ gpow i) :
    (honest P fs H C hdr T).read (gpow i) = some 0 :=
  image_read_zero h.lt_64 i hn

/-! ## A placed tree -/

/-- **A placed instance**: its `HeapBuf` pointers are its `bufBases`, its `frameAddr`s the
addresses of their runs in its frame. -/
theorem HonestAtB.nodeAt {cert : String → V → ℕ} (h : HonestAtB S P fs H C hdr T cert rd args rets)
    {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    (allocDsts (I.t.events P)).map σ = I.bufBases.map (fun b => ofK (gpow b)) ∧
      ∀ q ∈ addrs (I.t.events P), σ q.1 = ofK (gpow (I.fp + cert f q.2)) :=
  Inst.nodeAt (insts_placedAt T 0 hdr h.placed I hI) (insts_placed T 0 hdr I hI) ht

/-- **A memory holding the frames**: a placed tree valid on a memory holding every frame write
is `HonestAtB`, its equations consistent and agreeing with the frames. -/
theorem honestAtB_of_read {cert : String → V → ℕ} {M : MemImage (logMem (T.total fs))}
    (hv : T.ValidB S P M.read args rets) (hb : T.BufsOk P) (hp : T.Placed P fs cert 0)
    (hsize : T.total fs ≤ 2 ^ 32) (hcells : CellsOk fs C (honestInsts P fs H hdr T))
    (haddr : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = gpow i)
    (hf : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), M.read a.1 = some a.2) :
    HonestAtB S P fs H C hdr T cert M.read args rets := by
  have hκ : logMem (T.total fs) < 64 := by
    have := logMem_le_maxLogMem hsize; unfold maxLogMem at this; omega
  exact ⟨⟨hv, hsize, hcells, haddr, hv.eqns_consistent hκ haddr,
    cross_of_read hf fun b hb => hv.eqns_read hκ T b hb (haddr b hb)⟩, hb, hp⟩

/-- **A `frameAddr`'s equations are frame writes** of a placed instance whose cells hold its run
at the certificate's offsets. -/
theorem HonestAtB.frameAddr_eqns {cert : String → V → ℕ}
    (h : HonestAtB S P fs H C hdr T cert rd args rets) {I : Inst} (hI : I ∈ honestInsts P fs H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {p r : V} {rs : List V} (he : Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events P)
    (hrun : ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I) :
    ∀ q ∈ atomEqns σ (.frameAddr p (r :: rs)), q ∈ frameWrites C (honestInsts P fs H hdr T) := by
  intro q hq
  have hp := (h.nodeAt hI ht).2 (p, r) (List.mem_filterMap.mpr ⟨_, he, rfl⟩)
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
  refine List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨(cert f r + k, σ (r :: rs)[k]),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hrun k hk)), ?_⟩⟩
  simp only at hp ⊢
  rw [hp]
  rw [show (ofK (gpow (I.fp + cert f r))).limb 0 = gpow (I.fp + cert f r) by simp, gpow, gpow,
    gpow, ← pow_add, Nat.add_assoc]

/-! ## Certificates -/

/-- **Every value reads back** at its certificate cell. -/
theorem HonestB.read_value (h : HonestB S P fs H C hdr T rd args rets) {cert : String → V → ℕ}
    {dom : Inst → List V} (hC : ∀ I, valueCells cert dom I ⊆ C I) {I : Inst}
    (hI : I ∈ honestInsts P fs H hdr T) {v : V} (hv : v ∈ dom I) :
    (honest P fs H C hdr T).read (gpow I.fp * gpow (cert I.t.name v)) = some (I.t.val v) :=
  h.read_C hI (hC I (mem_valueCells hv))

end Honest


/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program} {fs : String → ℕ} {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)}
  {hdr : E × E} {T : Tree} {rd : Reader}

/-- At the deployed semantics, a good instance is `Memory.lean`'s. -/
theorem inst_goodB_deployed (I : Inst) : I.GoodB blakeDeployed P rd = I.Good P rd := by
  simp only [Inst.GoodB, Inst.Good, validB_deployed]

/-- **At the deployed semantics, `HonestB` is `Memory.lean`'s `Honest`.** -/
theorem honestB_deployed (args rets : List E) :
    HonestB blakeDeployed P fs H C hdr T rd args rets = Honest P fs H C hdr T rd args rets := by
  apply propext
  constructor <;> intro h <;> cases h <;> constructor <;>
    first | assumption | (simp only [validB_deployed] at *; assumption)

/-- **At the deployed semantics, `HonestAtB` is `Memory.lean`'s `HonestAt`.** -/
theorem honestAtB_deployed (cert : String → V → ℕ) (args rets : List E) :
    HonestAtB blakeDeployed P fs H C hdr T cert rd args rets =
      HonestAt P fs H C hdr T cert rd args rets := by
  apply propext
  constructor <;> intro ⟨h, hb, hp⟩
  · exact ⟨honestB_deployed args rets ▸ h, hb, hp⟩
  · exact ⟨(honestB_deployed args rets).symm ▸ h, hb, hp⟩

end Deployed

end
end LeanVM.Guest.Memory
