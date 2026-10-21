/-
  LeanVM.Guest.B1.Tables.VerifyTablesBaseM

  `verify_tables`' body under any semantics of `BLAKE2S`: its runs free of `BLAKE2S` hold as
  deployed, its Fiat-Shamir blocks over a hash model, and its windows evaluated by reflection.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBase
public import LeanVM.Guest.B1.Tables.VerifyTablesPoly
public import LeanVM.Guest.B1.Tables.GkrBaseM

/-!
# `verify_tables`' body under any semantics

`VerifyTablesBase.lean` over `S : BlakeSem`: `VtHoldsB S rd σ` says the valuation satisfies the
statements before the `ret` under `S` (`verify_tables_holdsB`). `verify_tables` calls the
functions of `vtFree` (`freeOn_vtFree`: free of `BLAKE2S` and closed under calls) and `__loop79`
(which runs `sumcheck_round4`); so

* `VtHoldsB.atom`, `VtHoldsB.slice`, `VtHoldsB.callIf`: an atom other than `BLAKE2S`, a run free
  of `BLAKE2S` over `vtFree`, a call of `vtFree`, hold as deployed (`VtHolds.atom`, …): every
  fact `VerifyTables*.lean` reads off such a run carries over with its proof;
* `VtHoldsB.callIfB`, `VtHoldsB.sliceB`: a call and a run under `S` (`__loop79`, the evaluations'
  blocks);
* `VtHoldsB.fsNext`, `VtHoldsB.squeeze`: the Fiat-Shamir blocks over a hash model, the new state
  the model's answer;
* `window_evalB`: `window_eval` under `S` (the reflection ignores `BLAKE2S` atoms,
  `symStepB_sound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The functions free of `BLAKE2S` -/

/-- The functions `verify_tables` calls that are free of `BLAKE2S` (all but `__loop79`), with every
function they call. -/
def vtFree : List String :=
  ["__loop12", "__loop13", "__loop14", "__loop15", "__loop16", "__loop17", "__loop18", "__loop19",
    "__loop20", "__loop21", "__loop22", "__loop23", "__loop24", "__loop25", "__loop26", "__loop27",
    "__loop28", "__loop29", "__loop30", "__loop31", "__loop32", "__loop33", "__loop34", "__loop35",
    "__loop36", "__loop37", "__loop38", "__loop39", "__loop40", "__loop41", "__loop42", "__loop43",
    "__loop44", "__loop45", "__loop46", "__loop47", "__loop48", "__loop49", "__loop50", "__loop51",
    "__loop52", "__loop53", "__loop54", "__loop55", "__loop56", "__loop57", "__loop58", "__loop59",
    "__loop60", "__loop61", "__loop62", "__loop63", "__loop64", "__loop65", "__loop66", "__loop67",
    "__loop68", "__loop69", "__loop70", "__loop71", "__loop72", "__loop73", "__loop74", "__loop75",
    "__loop76", "__loop77", "__loop78", "__loop80", "padding_weight__L0", "padding_weight__L1",
    "padding_weight__L2", "padding_weight__L3", "padding_weight__L4", "padding_weight__L5",
    "padding_weight__L6", "padding_weight__L7", "padding_weight__L8", "padding_weight__L9",
    "padding_weight__L10", "padding_weight__L11", "padding_weight__L12", "padding_weight__L13",
    "padding_weight__L14", "padding_weight__L15", "padding_weight__L16", "padding_weight__L17",
    "padding_weight__L18", "padding_weight__L19", "padding_weight__L20", "padding_weight__L21",
    "padding_weight__L22", "padding_weight__L23", "padding_weight__L24", "padding_weight__L25",
    "padding_weight__L26", "padding_weight__L27", "padding_weight__L28"]

/-- `vtFree` is free of `BLAKE2S` and closed under calls. -/
theorem freeOn_vtFree : coreProgram.FreeOn vtFree = true := by decide +kernel

variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-- **A function of `vtFree` under any semantics** is its deployed relation. -/
theorem relB_vtFree {f : String} (hf : f ∈ vtFree) (args rets : List E) :
    coreProgram.RelB S rd f args rets ↔ coreProgram.Rel rd f args rets :=
  relB_iff_rel_of_freeOn freeOn_vtFree hf args rets

/-- A run free of `BLAKE2S` over `vtFree` holds under `S` as deployed. -/
theorem holdsListB_vtFree {blk : List Stmt} (hf : Stmt.freeInList vtFree blk = true)
    {next : Prop} {kret : List E → Prop} :
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ blk next kret ↔
      Stmt.HoldsList (coreProgram.Rel rd) rd σ blk next kret := by
  rw [holdsListB_freeIn (S' := blakeDeployed) (C' := coreProgram.RelB blakeDeployed rd)
    (fun f hf a r => relB_eq_of_freeOn freeOn_vtFree (List.contains_iff_mem.mp hf) a r) blk hf,
    holdsListB_deployed, relB_deployed]

/-! ## The body -/

variable (S) in
/-- The valuation `σ` satisfies every statement of `verify_tables` before its `ret`, under `S`
(`VtHolds`). -/
def VtHoldsB (rd : Reader) (σ : Val) : Prop :=
  ∃ kret : List E → Prop, Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ vtPre True kret

/-- **`verify_tables`' relation under `S`** (`verify_tables_holds`). -/
theorem verify_tables_holdsB {args rets : List E}
    (h : coreProgram.RelB S rd "verify_tables" args rets) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15),
      σ (.n 16), σ (.n 17), σ (.n 18)] = args ∧ VtHoldsB S rd σ ∧
      [σ (.n 8171), σ (.n 8172), σ (.n 8175), σ (.n 8176), σ (.n 8177), σ (.n 8178)] = rets := by
  obtain ⟨σ, hp, hb, hr⟩ := relB_pre find_verify_tables core11_body vtPre_noRet h
  exact ⟨σ, hp, ⟨_, hb⟩, hr⟩

/-- A run of statements of the body holds under `S`. -/
theorem VtHoldsB.sliceB (h : VtHoldsB S rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vtPre.drop n).take blk.length) = true) :
    ∃ kret : List E → Prop, Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ blk True kret := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, holdsB_slice vtPre_noRet h n blk heq⟩

/-- **A run of the body free of `BLAKE2S`** holds as deployed (`VtHolds.slice`). -/
theorem VtHoldsB.slice (h : VtHoldsB S rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vtPre.drop n).take blk.length) = true)
    (hf : Stmt.freeInList vtFree blk = true) :
    ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True kret := by
  obtain ⟨k, h⟩ := h.sliceB n blk heq
  exact ⟨k, (holdsListB_vtFree hf).mp h⟩

/-- One atom of the body other than `BLAKE2S` holds as deployed (`VtHolds.atom`). -/
theorem VtHoldsB.atom (h : VtHoldsB S rd σ) (n : ℕ) (a : Atom)
    (heq : (stmtsEqb [.atom a] ((vtPre.drop n).take 1) && Stmt.noBlakeList [.atom a]) = true) :
    a.Holds rd σ := by
  obtain ⟨k, h⟩ := h
  exact holdsB_atom vtPre_noRet h n a heq

/-- `VtHoldsB.atom` with the absence of `BLAKE2S` given apart. -/
theorem VtHoldsB.atom' (h : VtHoldsB S rd σ) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] ((vtPre.drop n).take 1) = true)
    (hb : Stmt.noBlakeList [.atom a] = true) : a.Holds rd σ :=
  h.atom n a (by rw [heq, hb]; rfl)

/-- A conditional call of the body to a function of `vtFree` holds as deployed
(`VtHolds.callIf`). -/
theorem VtHoldsB.callIf (h : VtHoldsB S rd σ) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : (stmtsEqb [.callIf c f args] ((vtPre.drop n).take 1) &&
      Stmt.freeInList vtFree [.callIf c f args]) = true) :
    σ c ≠ 0 → coreProgram.Rel rd f (args.map σ) [] := by
  rw [Bool.and_eq_true] at heq
  obtain ⟨k, hs⟩ := h.slice n _ heq.1 heq.2
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at hs
  exact hs.2

/-- A conditional call of the body under `S`. -/
theorem VtHoldsB.callIfB (h : VtHoldsB S rd σ) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : stmtsEqb [.callIf c f args] ((vtPre.drop n).take 1) = true) :
    σ c ≠ 0 → coreProgram.RelB S rd f (args.map σ) [] := by
  obtain ⟨k, h⟩ := h
  exact holdsB_callIf vtPre_noRet h n c f args heq

/-- An `fs_next` of the body over a hash model (`VtHolds.fsNext`). -/
theorem VtHoldsB.fsNext {M : HashModel} (h : VtHoldsB M.sem rd σ) (n : ℕ) (s0 s1 cur : V)
    (j b : ℕ) (heq : stmtsEqb (fsNextT s0 s1 cur j b) ((vtPre.drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
      obsCvM M cv (σ (.n b)) = some d ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars d := by
  obtain ⟨k, h⟩ := h
  exact holdsB_fsNextAt vtPre_noRet h n s0 s1 cur j b heq

/-- A `squeeze` of the body over a hash model (`VtHolds.squeeze`). -/
theorem VtHoldsB.squeeze {M : HashModel} (h : VtHoldsB M.sem rd σ) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) ((vtPre.drop n).take 14) = true) :
    ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ sqCvM M cv = some d ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars d ∧ σ (.n (b + 13)) = challengeOf d := by
  obtain ⟨k, h⟩ := h
  exact holdsB_squeezeAt vtPre_noRet h n s0 s1 b heq

/-! ## Windows by reflection under any semantics -/

/-- An atom holding under `S` with no `BLAKE2S` holds as deployed. -/
theorem atom_holds_of_holdsB {a : Atom} (ha : a.HoldsB S rd σ)
    (hb : Stmt.noBlakeList [.atom a] = true) : a.Holds rd σ := by
  have h : Stmt.HoldsListB S (fun _ _ _ ↦ True) rd σ [.atom a] True (fun _ ↦ True) := by
    simpa [Stmt.HoldsListB, Stmt.HoldsB] using ha
  have := (holdsListB_iff_of_noBlake hb True (fun _ ↦ True)).mp h
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- `symStep_sound` under `S`: a `BLAKE2S` atom binds nothing. -/
theorem symStepB_sound {χ : ℕ → E} {L : LoadTab} (hL : L.Sound rd σ χ)
    {m : Binds} (hm : m.Sound (fun k => σ (.n k)) χ) {a : Atom} (ha : a.HoldsB S rd σ) :
    (symStep L m a).Sound (fun k => σ (.n k)) χ := by
  by_cases hb : Stmt.noBlakeList [.atom a] = true
  · exact symStep_sound hL hm (atom_holds_of_holdsB ha hb)
  · cases a with
    | blake2s => exact hm
    | _ => simp [Stmt.noBlakeList, Stmt.noBlake] at hb

/-- A run of atoms holding under `S`, symbolically (`symExec_sound`). -/
theorem symExecB_sound {χ : ℕ → E} {L : LoadTab} (hL : L.Sound rd σ χ) :
    ∀ (atoms : List Atom) (m : Binds), m.Sound (fun k => σ (.n k)) χ →
      (∀ a ∈ atoms, a.HoldsB S rd σ) → (symExec L m atoms).Sound (fun k => σ (.n k)) χ
  | [], _, hm, _ => hm
  | a :: rest, _, hm, h =>
    symExecB_sound hL rest _ (symStepB_sound hL hm (h a (List.mem_cons_self ..)))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The atoms of a block without `ret` hold under `S`, once the block does (`atoms_hold`). -/
theorem atoms_holdB {C : CallRel} {kret : List E → Prop} :
    ∀ (ss : List Stmt), Stmt.noRetList ss = true → Stmt.HoldsListB S C rd σ ss True kret →
      ∀ a ∈ ss.filterMap atomOf, a.HoldsB S rd σ
  | [], _, _ => by simp
  | s :: ss, hnr, h => by
    simp only [Stmt.noRetList, Bool.and_eq_true] at hnr
    simp only [Stmt.HoldsListB] at h
    rw [holdsB_noRet s hnr.1] at h
    intro a ha
    cases s with
    | atom b =>
      simp only [List.filterMap_cons, atomOf, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simpa [Stmt.HoldsB] using h.1
      · exact atoms_holdB ss hnr.2 h.2 a ha
    | _ =>
      simp only [List.filterMap_cons, atomOf] at ha
      exact atoms_holdB ss hnr.2 h.2 a ha

/-- **A value of a window of a body under `S`, by reflection** (`window_eval`). -/
theorem window_evalB {C : CallRel} {kret : List E → Prop} {pre : List Stmt}
    (hnr : Stmt.noRetList pre = true) (h : Stmt.HoldsListB S C rd σ pre True kret) {χ : ℕ → E}
    {L : LoadTab} (hL : L.Sound rd σ χ) (n len k : ℕ) (e : Ex)
    (heq : ((symExec L [] (((pre.drop n).take len).filterMap atomOf)).get k).norm = e.norm) :
    σ (.n k) = e.eval (fun k => σ (.n k)) χ := by
  have hs := symExecB_sound hL (((pre.drop n).take len).filterMap atomOf) []
    (fun _ h => by simp at h)
    (fun a ha => atoms_holdB pre hnr h a (List.mem_filterMap.mpr (by
      obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp ha
      exact ⟨s, List.mem_of_mem_drop (List.mem_of_mem_take hs), hsa⟩)))
  rw [Binds.get_sound hs k]
  exact Ex.eval_eq_of_norm heq _ _

end
end LeanVM.Guest.B1.VerifySub
