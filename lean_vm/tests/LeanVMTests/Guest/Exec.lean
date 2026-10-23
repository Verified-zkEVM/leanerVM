import LeanVM.Guest.Check

/-!
# The symbolic executor and the checker's bounds on guest functions

`exec` evaluated by the kernel on compiled functions of the guest:

* `assert_canonical`, straight code: its one segment, its atoms, and its contract by `exec_sound`,
  the run returning in fewer steps;
* `da_hash_roots__L0`, straight code with a `KECCAK`: its contract gives `KeccakCells` of the
  thirteen cells it reads (`m0..m3`, the runs from `tail` and `cap`, `b8`) and the thirteen it
  writes;
* the selectors bounded by booleanity (`Check.selBound`): `r_g` of `shared_selector_tables`
  (`(1 + b₀(1 + g))(1 + b₁(1 + g²))`, below `g^4`) and `odd_g` of `verify_keccak`
  (`1 + b(1 + g)`, below `g^2`), from the atoms of the functions' paths.
-/

namespace LeanVMTests.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

def F0 : Facts := {}

/-! ## `assert_canonical` -/

/-- Its atoms: the instructions it executes, the not-taken `JUMP` reading its cells in `K`, and
the return. -/
def canonicalAtoms : List Atom :=
  [.instr 9254 (.xor 2 4 5), .instr 9255 (.set 6 1 0 1), .instr 9256 (.mul 5 6 7),
    .instr 9257 (.set 8 0 0 0), .jump 8 4 7, .instr 9259 (.set 3 0 0 0),
    .instr 9260 (.set 9 1 0 0), .jump 9 0 1]

theorem canonical_name : Data.f2.name = "assert_canonical" := by decide +kernel

theorem canonical_shape : (exec F0 Data.f2).segs.map (fun s ↦ (s.start, s.env.sub Sym.beq .nil,
    (branchExits s.items).isEmpty, s.items.filterMap Item.atom?, s.exit.kind)) =
      [(0, true, true, canonicalAtoms, .ret)] := by
  decide +kernel

/-- **`assert_canonical`'s contract**, from the executor: a halting run entering it returns, in
fewer steps, with every atom holding. -/
theorem canonical_spec {κ : ℕ} {L : MemImage κ} (hκ : κ ≤ 32) :
    FunSpec guest L 9254 (fun _ ↦ True) (fun fp ↦ ∀ a ∈ canonicalAtoms, a.Holds L fp) := by
  intro fp k _ h
  obtain ⟨s, hs, he⟩ := List.mem_map.mp (canonical_shape ▸ List.mem_singleton_self _)
  simp only [Prod.mk.injEq] at he
  obtain ⟨h0, henv, hb, hatoms, hkind⟩ := he
  have hctx : Ctx F0 κ fp := ⟨trivial, fun h ↦ absurd h (by decide), hκ⟩
  have hentry : Data.f2.entry + s.start = 9254 := by rw [h0]; rfl
  have hrun := exec_sound hctx (guest_fetches (mem_functions (j := 2) rfl)) hs
    (EnvHolds.nil.sub henv) (hentry ▸ h)
  obtain ⟨hall, k', -, hlt, -, -, r, hr, hsafe⟩ :=
    RunK.straight (List.isEmpty_iff.mp hb) hrun
  rw [hkind] at hr
  exact ⟨k', hlt, r, hr, hatoms ▸ hall, hsafe⟩

/-! ## A `KECCAK`: `da_hash_roots__L0` -/

/-- Its `KECCAK`: the thirteen cells `fp[18], fp[19], fp[19], fp[19]`, `fp[19..22]`, `fp[23]`,
`fp[19..22]`, in the even layout, to `fp[5..17]`, in the even layout. -/
def hashIns : OInstr := .keccak 18 19 19 19 19 23 19 5 false false

theorem hash_name : Data.f378.name = "da_hash_roots__L0" ∧ Data.f378.entry = 276079 := by
  decide +kernel

theorem hash_shape : (exec F0 Data.f378).segs.map (fun s ↦ (s.start, s.env.sub Sym.beq .nil,
    (branchExits s.items).isEmpty, (s.items.filterMap Item.atom?).contains (.instr 276085 hashIns),
      s.exit.kind)) = [(0, true, true, true, .ret)] := by
  decide +kernel

/-- **`da_hash_roots__L0`'s contract**: a halting run entering it returns, in fewer steps, with
its `KECCAK` holding: the cells it reads hold a state whose Keccak-f[1600] the cells it writes
hold. -/
theorem hash_spec {κ : ℕ} {L : MemImage κ} (hκ : κ ≤ 32) :
    FunSpec guest L 276079 (fun _ ↦ True) (fun fp ↦ ∃ input output : Fin 13 → E,
      (∀ c : Fin 13, L.read (fp * gpow (keccakInOff 18 19 19 19 19 23 19 c.val)) = some (input c)) ∧
      (∀ c : Fin 13, L.read (fp * gpow (5 + c.val)) = some (output c)) ∧
      KeccakCells input false output false) := by
  intro fp k _ h
  obtain ⟨s, hs, he⟩ := List.mem_map.mp (hash_shape ▸ List.mem_singleton_self _)
  simp only [Prod.mk.injEq] at he
  obtain ⟨h0, henv, hb, hmem, hkind⟩ := he
  have hctx : Ctx F0 κ fp := ⟨trivial, fun h ↦ absurd h (by decide), hκ⟩
  have hentry : Data.f378.entry + s.start = 276079 := by rw [h0]; rfl
  have hrun := exec_sound hctx (guest_fetches (mem_functions (j := 378) rfl)) hs
    (EnvHolds.nil.sub henv) (hentry ▸ h)
  obtain ⟨hall, k', -, hlt, -, -, r, hr, hsafe⟩ :=
    RunK.straight (List.isEmpty_iff.mp hb) hrun
  rw [hkind] at hr
  exact ⟨k', hlt, r, hr, hall _ (List.elem_iff.mp hmem), hsafe⟩

/-! ## Selectors bounded by booleanity -/

open LeanVM.Guest.Check in
/-- The atoms of every path of a function, filed in one book. -/
noncomputable def bookOf (f : CompiledFn) : Book :=
  ((exec F0 f).segs.flatMap fun s ↦ s.items.filterMap Item.atom?).foldl addFact .nil

theorem names : Data.f10.name = "shared_selector_tables" ∧ Data.f13.name = "verify_keccak" := by
  decide +kernel

open LeanVM.Guest.Check in
/-- `r_g = (1 + b₀(1 + g))(1 + b₁(1 + g²))` in `fp[21]`, the selector of the dispatch on
`log(r_g)` over four arms: `g^e` with `e < 4`. -/
theorem r_g_bound : selBound (bookOf Data.f10) selFuel 21 = some 4 := by decide +kernel

open LeanVM.Guest.Check in
/-- `odd_g = 1 + b(1 + g)` in `fp[61]`, the selector of `verify_keccak`'s twelve dispatches on
`log(odd_g)` over two arms: `g^e` with `e < 2`. -/
theorem odd_g_bound : selBound (bookOf Data.f13) selFuel 61 = some 2 := by decide +kernel

open LeanVM.Guest.Check in
/-- A selector bound is only claimed of such a selector: `fp[60] = b·(1 + g)` is none. -/
theorem odd_g_scaled_none : selBound (bookOf Data.f13) selFuel 60 = none := by decide +kernel

end LeanVMTests.Guest.Exec
