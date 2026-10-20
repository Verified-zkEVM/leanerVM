/-
  LeanVM.Guest.B1.Da.Verify

  B1 for `da_verify` (G:2888-2956), soundly: its relation implies that a LeanDA witness opens the
  returned root and vector digest (`Da.Witness.Opens`).
-/

module

public import LeanVM.Guest.B1.Da.Named
public import LeanVM.Guest.B1.Da.ListDigest

/-!
# `da_verify`, soundly

From `DaFacts`: each column's and each cell's facts (`Da.Columns`), each row's digest, then the
witness, the rows' symbols and the vector's weights, and its four properties: the vector digest
is the chain of the `128` columns' hashes (`vector_chain`), the rows' inner products telescope to
the row sums' ends, `0` (`dot_eq`), and the commitment is the hash of the row tree's root and the
column tree's (`commitCodewords_eq`).

**The witness, named** (`da_verify_sound_w`). On a valuation `σ` of `da_verify`'s body, under any
call relation below the program's whose column loops `__loop90`, `__loop91` give their columns'
witnesses `w90 args rets`, `w91 args rets` (`ColsOut`, `Da.Named`), the witness `dvWit σ w90 w91`
(the columns' cells as rows, their weights as the vector) holds the claim of the returned words
(`DaOut`: they decode to a root and a vector digest that it opens). `da_verify_sound` follows, its
witness functions chosen.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-- **The witness of the guest's cells**: `r` rows, row `i` the cells `sy b i` of the `128`
columns in order, and the vector the `128` chunks `ws b`. -/
def daWitOf (r : ℕ) (sy : ℕ → ℕ → List K) (ws : ℕ → List E) : Da.Witness :=
  ⟨(List.range r).map fun i => (List.range 128).flatMap fun b => sy b i, (List.range 128).flatMap ws⟩

theorem daWitOf_congr {r : ℕ} {sy sy' : ℕ → ℕ → List K} {ws ws' : ℕ → List E}
    (hsy : ∀ b < 128, ∀ i < r, sy b i = sy' b i) (hws : ∀ b < 128, ws b = ws' b) :
    daWitOf r sy ws = daWitOf r sy' ws' := by
  unfold daWitOf
  congr 1
  · refine List.map_congr_left fun i hi => List.flatMap_congr fun b hb => ?_
    exact hsy b (List.mem_range.mp hb) i (List.mem_range.mp hi)
  · exact List.flatMap_congr fun b hb => hws b (List.mem_range.mp hb)

/-- **`da_verify`, soundly, its witness given**: the facts other than the columns', each column's
facts `F b` and each of its cells' `G b i` give the witness of the cells' symbols and the columns'
weights (`daWitOf`), which opens the returned root and vector digest. -/
theorem opens_of {rd : Reader} {r0 r1 v0 v1 : E} {r : ℕ} {pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E}
    (h : DaRest rd r pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1) (F : ℕ → ColW)
    (G : ℕ → ℕ → CellW) (hF : ∀ b < 128, ColOk rd r pb ct rb hs b (F b))
    (hG : ∀ b < 128, ∀ i < r,
      CellOk rd (decide (b < 64)) (F b).lv rb (gen ^ b) (F b).node pb (gen ^ i) (G b i)) :
    (r0, r1) = digestScalars (commitOf r fun b i => (G b i).syms) ∧
      (v0, v1) = digestScalars (blake2sBytes (((List.range 128).flatMap fun b => (F b).ws).flatMap eBytes)) ∧
      (daWitOf r (fun b i => (G b i).syms) (fun b => (F b).ws)).Opens (commitOf r fun b i => (G b i).syms)
        (blake2sBytes (((List.range 128).flatMap fun b => (F b).ws).flatMap eBytes)) := by
  obtain ⟨hr1, hr2, -, hiv0, hiv1, -, -, h89, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  obtain ⟨hrN, hNr⟩ := (logPad_iff (lp := LeanDa.logPad r) hr1).mp rfl
  have hNdef : LeanDa.nPad r = 2 ^ LeanDa.logPad r := rfl
  obtain ⟨Rw, hRw⟩ := choose_lt (α := E × List E) (n := r) (P := fun i x =>
      LoadHolds rd (pb * gen ^ i) 0 x.1 ∧ x.2.length = 128 ∧ CellsAt rd x.1 x.2 ∧
        (∀ c ∈ x.2, IsCanonical128 c) ∧
        CellsAt rd (rt * (gen ^ i * gen ^ i)) [(digestScalars (blake2sBytes (x.2.flatMap cellBytes))).1,
          (digestScalars (blake2sBytes (x.2.flatMap cellBytes))).2])
    (fun i hi => by obtain ⟨P, cs, h⟩ := h93 i hi; exact ⟨(P, cs), h⟩)
  -- the witness
  let sy : ℕ → ℕ → List K := fun b i => (G b i).syms
  let rowL : ℕ → List K := fun i => (List.range 128).flatMap fun b => sy b i
  let rows : List (List K) := (List.range r).map rowL
  let vector : List E := (List.range 128).flatMap fun b => (F b).ws
  have hsyl : ∀ b < 128, ∀ i < r, (sy b i).length = 256 := fun b hb i hi => (hG b hb i hi).1
  have hrowL : ∀ i < r, (rowL i).length = 2 ^ LeanDa.logM := fun i hi => by
    rw [length_flatMap_range _ 128 (fun b hb => hsyl b hb i hi)]; rfl
  -- the column roots
  have hcolroot : ∀ b < 128, ((F b).c0, (F b).c1) = digestScalars (nodeD (colLeafOf r sy b) (LeanDa.logPad r) 0) := by
    intro b hb
    obtain ⟨-, -, -, -, -, -, hgap, hlv, -⟩ := hF b hb
    refine levels_root hlv fun i hi => ?_
    rw [← hNdef] at hi
    by_cases hir : i < r
    · obtain ⟨-, -, -, hd, -, -, -, -, hn, -⟩ := hG b hb i hir
      simp only [colLeafOf, cellDOf, hir, ↓reduceIte]
      rw [gen_sq] at hn
      rw [← hd]; exact hn
    · have := hgap (i - r) (by omega)
      simp only [colLeafOf, hir, ↓reduceIte, padCell_cells]
      unfold GapStep at this
      rwa [pad_ptr, show r + (i - r) = i by omega] at this
  have hRC : (rc0, rc1) = digestScalars (colRootOf r sy) := by
    refine levels_root hlv7 fun b hb => ?_
    rw [← hcolroot b (by simpa using hb)]
    exact (hF b (by simpa using hb)).2.2.2.2.2.2.2.2
  -- the row digests
  have hcs : ∀ i < r, (Rw i).2.flatMap cellBytes = (List.range 64).flatMap fun b => digestBytes (cellDOf sy b i) := by
    intro i hi
    obtain ⟨hP, hlen, hcells, -, -⟩ := hRw i hi
    have hc2 : ∀ b < 64, (Rw i).2.getD (2 * b) 0 = (G b i).d0 ∧ (Rw i).2.getD (2 * b + 1) 0 = (G b i).d1 := by
      intro b hb
      obtain ⟨-, -, -, -, -, -, -, -, -, hst⟩ := hG b (by omega) i hi
      obtain ⟨P', hP', hc⟩ := hst (decide_eq_true hb)
      rw [loadHolds_unique hP' hP, gen_sq] at hc
      obtain ⟨x0, x1⟩ := cellsAt_two.mp hc
      rw [loadHolds_mul_gen_pow] at x0 x1
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact ⟨loadHolds_unique (hcells _ (by omega)) x0, loadHolds_unique (hcells _ (by omega)) x1⟩
    rw [← flatMap_range_getD (Rw i).2 0 cellBytes, hlen, show 128 = 2 * 64 by rfl, flatMap_range_mul 2]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    rw [show List.range 2 = [0, 1] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
    rw [(hc2 b hb').1, (hc2 b hb').2, digestBytes_eq, cellDOf, ← (hG b (by omega) i hi).2.2.2.1]
  have hRR : (rr0, rr1) = digestScalars (rowRootOf r sy) := by
    refine levels_root hlvr fun i hi => ?_
    rw [← hNdef] at hi
    by_cases hir : i < r
    · obtain ⟨-, -, -, -, hout⟩ := hRw i hir
      simp only [rowLeafOf, hir, ↓reduceIte, rowDOf]
      rw [gen_sq, hcs i hir] at hout
      exact hout
    · have := h94 (i - r) (by omega)
      simp only [rowLeafOf, hir, ↓reduceIte, padRow_cells]
      unfold L94Step at this
      rwa [pad_ptr, show r + (i - r) = i by omega] at this
  refine ⟨?_, vector_chain hF hiv0 hiv1 hv0 hv1, ?_⟩
  · obtain ⟨e1, e2⟩ := Prod.mk.inj hRR
    obtain ⟨e3, e4⟩ := Prod.mk.inj hRC
    rw [e1, e2, e3, e4] at hfin
    exact compress_pair.mp hfin
  have hlen : rows.length = r := by simp [rows]
  change (⟨rows, vector⟩ : Da.Witness).Opens _ _
  refine ⟨by simp only [hlen]; exact hr1, by simp only [hlen]; exact hr2, fun row hrow => ?_, ?_, ?_,
    vectorDigest_eq vector, fun row hrow => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    exact hrowL i (List.mem_range.mp hi)
  · rw [commitCodewords_eq (by rw [hlen]; exact hr1) fun i hi b hb => ?_, hlen]
    simp only [rows, List.getElem_map, List.getElem_range]
    exact listCell_flatMap (fun b => sy b i) (fun b hb => hsyl b hb i (by rw [← hlen]; exact hi)) hb
  · show vector.length = _
    rw [length_flatMap_range _ 128 (fun b hb => (hF b hb).1)]; rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range.mp hi
    have hws : ∀ b < 128, ∀ k < 256, (G b i).wsc.getD k 0 = (F b).ws.getD k 0 := by
      intro b hb k hk
      obtain ⟨-, hwl, hcells, -⟩ := hG b hb i hi'
      obtain ⟨-, -, -, -, hfr, -⟩ := hF b hb
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hfr.2 k (by rw [(hF b hb).1]; exact hk) _ (hcells k (by omega)).2
    let Ri : E := acc * (gen ^ i) ^ 129
    have hR : ∀ b < 128, (G b i).R = Ri := fun b hb =>
      loadHolds_unique (hG b hb i hi').2.2.2.2.2.1 (h89 i hi').1
    have hA : ∀ b < 128, (G b i).s = cellAt rd Ri (b + 1) - cellAt rd Ri b := by
      intro b hb
      obtain ⟨-, -, -, -, -, -, ha, has, -⟩ := hG b hb i hi'
      rw [hR b hb, loadHolds_mul_gen_pow] at ha has
      have e0 : cellAt rd Ri b = (G b i).a := cellAt_of_load ha
      have e1 : cellAt rd Ri (b + 1) = (G b i).a + (G b i).s := cellAt_of_load has
      rw [e0, e1]
      ring
    have h0 : cellAt rd Ri 0 = 0 := cellAt_of_load (h89 i hi').2
    have h128 : cellAt rd Ri 128 = 0 := by
      obtain ⟨R', hR', h1⟩ := h92 i hi'
      rw [loadHolds_unique hR' (h89 i hi').1] at h1
      exact cellAt_of_load h1
    rw [dot_eq rfl rfl (fun b hb => (hF b hb).1) (fun b hb => hsyl b hb i hi')]
    rw [Finset.sum_congr rfl (g := fun b => (G b i).s) fun b hb => by
        have hb' := Finset.mem_range.mp hb
        rw [(hG b hb' i hi').2.2.2.2.1]
        exact Finset.sum_congr rfl fun k hk => by rw [hws b hb' k (Finset.mem_range.mp hk)],
      Finset.sum_congr rfl (fun b hb => hA b (Finset.mem_range.mp hb)), Finset.sum_range_sub, h128, h0, sub_zero]

/-- **`da_verify`, soundly**: the facts of its relation give a witness that opens the returned
root and vector digest. -/
theorem daFacts_opens {rd : Reader} {r0 r1 v0 v1 : E} (h : DaFacts rd r0 r1 v0 v1) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧
      w.Opens root vd := by
  obtain ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hr1, hr2, h88, hiv0, hiv1, hk, hctr, h89,
    hcol, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  obtain ⟨F, hF⟩ := choose_lt (fun b hb => col_facts hr1 hr2 hctr hb (hcol b hb))
  obtain ⟨G, hG⟩ := choose_lt₂ (n := 128) (m := r) (P := fun b i c =>
      CellOk rd (decide (b < 64)) (F b).lv rb (gen ^ b) (F b).node pb (gen ^ i) c)
    (fun b hb i hi => cell_facts ((hF b hb).2.2.2.2.2.1 i hi))
  obtain ⟨e1, e2, ho⟩ := opens_of ⟨hr1, hr2, h88, hiv0, hiv1, hk, hctr, h89, h92, hlv7, h93, h94, hlvr, hfin,
    hv0, hv1⟩ F G hF hG
  exact ⟨_, _, _, e1, e2, ho⟩

/-! ## The witness, named -/

/-- `Witness.Opens` is decidable (noncomputably: LeanDA's inner product is). -/
noncomputable instance (root vd : Digest) (w : Da.Witness) : Decidable (w.Opens root vd) := by
  unfold Da.Witness.Opens; infer_instance

/-- **`da_verify`'s outcome, its witness named** `w`: the returned words `r0, r1` and `v0, v1`
decode to a root and a vector digest (`digestOfScalars`) that `w` opens. The memory and the
argument (`rd`, `gsq`) are not needed. -/
def DaOut (_rd : Reader) (_gsq : E) (r0 r1 v0 v1 : E) (w : Da.Witness) : Prop :=
  ∃ root ∈ digestOfScalars (r0, r1), ∃ vd ∈ digestOfScalars (v0, v1), w.Opens root vd

noncomputable instance (rd : Reader) (gsq r0 r1 v0 v1 : E) (w : Da.Witness) :
    Decidable (DaOut rd gsq r0 r1 v0 v1 w) := by
  unfold DaOut; infer_instance

/-- `DaOut` is the old conclusion with the witness given. -/
theorem daOut_iff {rd : Reader} {gsq r0 r1 v0 v1 : E} {w : Da.Witness} :
    DaOut rd gsq r0 r1 v0 v1 w ↔
      ∃ root vd : Digest, (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧ w.Opens root vd := by
  constructor
  · rintro ⟨root, h1, vd, h2, h⟩
    exact ⟨root, vd, (digestScalars_digestOfScalars h1).symm, (digestScalars_digestOfScalars h2).symm, h⟩
  · rintro ⟨root, vd, h1, h2, h⟩
    refine ⟨root, ?_, vd, ?_, h⟩
    · rw [h1]; exact digestOfScalars_digestScalars root
    · rw [h2]; exact digestOfScalars_digestScalars vd

/-- `da_verify`'s column `b`: item `b` of `__loop90`'s columns, or item `b - 64` of `__loop91`'s. -/
def dvCol (σ : Val) (w90 w91 : List E → List E → List DaColumn) (b : ℕ) : DaColumn :=
  if b < 64 then (w90 (dvColArgs σ (.n 420)) []).getD b default
  else (w91 (dvColArgs σ (.n 421)) []).getD (b - 64) default

/-- **`da_verify`'s witness**: the rows of its `128` columns' cells, as many as column `0` has,
and the vector of their weights. -/
def dvWit (σ : Val) (w90 w91 : List E → List E → List DaColumn) : Da.Witness :=
  daWitOf (dvCol σ w90 w91 0).cells.length (fun b i => (dvCol σ w90 w91 b).cells.getD i [])
    (fun b => (dvCol σ w90 w91 b).weights)

/-- **`da_verify`, soundly, its witness named**: on a valuation of its body under a call relation
below the program's, whose column loops give their columns' witnesses `w90`, `w91`, the returned
words are a root and a vector digest that `dvWit σ w90 w91` opens. -/
theorem da_verify_sound_w {C : CallRel} {rd : Reader} (hC : CallRel.Le C (coreProgram.Rel rd))
    (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq) {w90 w91 : List E → List E → List DaColumn}
    (h90 : ∀ args rets, C "__loop90" args rets → ColsOut true rd args rets (w90 args rets))
    (h91 : ∀ args rets, C "__loop91" args rets → ColsOut false rd args rets (w91 args rets))
    {σ : Val} {r0 r1 v0 v1 : E} (hp : ([.n 0] : List V).map σ = [gsq])
    (hb : Stmt.HoldsList C rd σ dvBody False (fun rs => rs = [r0, r1, v0, v1])) :
    DaOut rd gsq r0 r1 v0 v1 (dvWit σ w90 w91) := by
  obtain ⟨r, c420, c421, hnb, hnp, hgap, hglp, hrest, hc90, hc91⟩ := da_verify_rest hC hm hT hp hb
  obtain ⟨hr1, hr2, -, -, -, -, hctr, -⟩ := id hrest
  -- the prefix columns
  obtain ⟨x, ps, ha, -, hl⟩ := h90 _ _ hc90
  unfold dvColArgs at ha
  rw [c420, hnb, hnp, hgap, hglp] at ha
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  rw [colLoopEnd_eq, ite_pos' rfl] at hl
  obtain ⟨hl90, hB90⟩ := loopW_one (n := 64) (by norm_num) (by norm_num) hl
  -- the other columns
  obtain ⟨x, ps', ha, -, hl⟩ := h91 _ _ hc91
  unfold dvColArgs at ha
  rw [c421, hnb, hnp, hgap, hglp] at ha
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  rw [colLoopEnd_eq, ite_neg' (by decide)] at hl
  obtain ⟨hl91, hB91⟩ := loopW_pow (a := 64) (n := 64) (by norm_num) (by norm_num) hl
  -- each column, and its cells
  have hcol : ∀ b < 128, ColOutW (decide (b < 64)) rd [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r,
      gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, σ (.n 13), σ (.n 419), σ (.n 415), σ (.n 17),
      σ (.n 405)] [] (dvCol σ w90 w91 b) := by
    intro b hb
    unfold dvCol
    by_cases h64 : b < 64
    · rw [ite_pos' h64, decide_eq_true h64, List.getD_eq_getElem _ _ (by omega)]
      exact hB90 b (by omega)
    · rw [ite_neg' h64, decide_eq_false h64, List.getD_eq_getElem _ _ (by omega)]
      have := hB91 (b - 64) (by omega)
      rwa [show 64 + (b - 64) = b by omega] at this
  obtain ⟨F, hF⟩ := choose_lt (fun b hb => col_facts_w hr1 hr2 hctr hb (hcol b hb))
  obtain ⟨G, hG⟩ := choose_lt₂ (n := 128) (m := r) (P := fun b i g =>
      CellOk rd (decide (b < 64)) (F b).lv (σ (.n 415)) (gen ^ b) (F b).node (σ (.n 13)) (gen ^ i) g ∧
        g.syms = (dvCol σ w90 w91 b).cells.getD i [])
    (fun b hb i hi => (hF b hb).2.2.2 i hi)
  obtain ⟨e1, e2, ho⟩ := opens_of hrest F G (fun b hb => (hF b hb).1) (fun b hb i hi => (hG b hb i hi).1)
  have hw : daWitOf r (fun b i => (G b i).syms) (fun b => (F b).ws) = dvWit σ w90 w91 := by
    unfold dvWit
    rw [(hF 0 (by norm_num)).2.2.1]
    exact daWitOf_congr (fun b hb i hi => (hG b hb i hi).2) (fun b hb => (hF b hb).2.1)
  rw [← hw]
  exact daOut_iff.mpr ⟨_, _, e1, e2, ho⟩

/-! ## The old statement, its witness functions chosen -/

/-- A witness function for a relation each of whose pairs has a witness. -/
theorem exists_witFn {α : Type} [Inhabited α] {P : List E → List E → Prop} {Q : List E → List E → α → Prop}
    (h : ∀ a r, P a r → ∃ w, Q a r w) : ∃ wf : List E → List E → α, ∀ a r, P a r → Q a r (wf a r) := by
  classical
  exact ⟨fun a r => if hp : P a r then (h a r hp).choose else default, fun a r hp => by
    simp only [hp, ↓reduceDIte]; exact (h a r hp).choose_spec⟩

/-- **A self-calling function's pairs have witnesses** when one frame's do, given its own calls'
witness function, under every call relation below the program's. -/
theorem rel_witness {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {α : Type}
    [Inhabited α] {Q : List E → List E → α → Prop}
    (step : ∀ C : CallRel, CallRel.Le C (coreProgram.Rel rd) → ∀ wl : List E → List E → α,
      (∀ a r, C f a r → Q a r (wl a r)) → ∀ (σ : Val) (args rets : List E), fn.params.map σ = args →
        Stmt.HoldsList C rd σ fn.body False (fun rs => rs = rets) → ∃ w, Q args rets w) :
    ∀ args rets, coreProgram.Rel rd f args rets → ∃ w, Q args rets w := by
  rintro args rets ⟨n, h⟩
  induction n generalizing args rets with
  | zero => exact h.elim
  | succ n ih =>
    obtain ⟨fn', hf', σ, hp, hb⟩ := h
    rw [hf] at hf'
    cases hf'
    obtain ⟨wl, hwl⟩ := exists_witFn (P := coreProgram.relN rd n f) ih
    exact step _ (relN_le_rel coreProgram n) wl hwl σ args rets hp hb

theorem vecOut_exists (final : Bool) {rd : Reader} :
    ∀ args rets, coreProgram.Rel rd (vxName final) args rets → ∃ ws, VecOut final rd args rets ws :=
  fun args rets h => by
    rw [rel_of_find (find_vx final)] at h
    obtain ⟨σ, hp, hb⟩ := h
    exact ⟨_, da_vector_cell_out hp hb⟩

theorem vdOut_exists {rd : Reader} :
    ∀ args rets, coreProgram.Rel rd "da_vector_dispatch" args rets → ∃ ws, VdOut rd args rets ws :=
  fun args rets h => by
    rw [rel_of_find find_vd] at h
    obtain ⟨σ, hp, hb⟩ := h
    obtain ⟨w1, h1⟩ := exists_witFn (vecOut_exists true (rd := rd))
    obtain ⟨w0, h0⟩ := exists_witFn (vecOut_exists false (rd := rd))
    exact ⟨_, vd_out (wv := fun f => if f then w1 else w0)
      (fun final a r hr => by cases final <;> [exact h0 a r hr; exact h1 a r hr]) hp hb⟩

theorem cellOut_exists {rd : Reader} :
    ∀ args rets, coreProgram.Rel rd "da_verify_cell" args rets → ∃ syms, CellOut rd args rets syms :=
  fun args rets h => by
    rw [rel_of_find find_da_verify_cell] at h
    obtain ⟨σ, hp, hb⟩ := h
    exact ⟨_, da_verify_cell_out hp hb⟩

theorem rowsOut_exists (store : Bool) {rd : Reader} :
    ∀ args rets, coreProgram.Rel rd (rowName store) args rets → ∃ L, RowsOut store rd args rets L := by
  obtain ⟨wc, hc⟩ := exists_witFn (cellOut_exists (rd := rd))
  exact rel_witness (find_row store) fun C hC wl hwl σ args rets hp hb =>
    ⟨_, row_loop_out store (fun a r h => hc a r (hC _ _ _ h)) hwl hp hb⟩

theorem colOutW_exists (store : Bool) {rd : Reader} :
    ∀ args rets, coreProgram.Rel rd (colName store) args rets → ∃ cw, ColOutW store rd args rets cw :=
  fun args rets h => by
    rw [rel_of_find (find_col store)] at h
    obtain ⟨σ, hp, hb⟩ := h
    obtain ⟨wd, hd⟩ := exists_witFn (vdOut_exists (rd := rd))
    obtain ⟨wr, hr⟩ := exists_witFn (rowsOut_exists store (rd := rd))
    exact ⟨_, col_out store (fun _ _ _ h => h) hd hr hp hb⟩

theorem colsOut_exists (store : Bool) {rd : Reader} :
    ∀ args rets, coreProgram.Rel rd (colLoopName store) args rets → ∃ L, ColsOut store rd args rets L := by
  obtain ⟨wc, hc⟩ := exists_witFn (colOutW_exists store (rd := rd))
  exact rel_witness (find_colLoop store) fun C hC wl hwl σ args rets hp hb =>
    ⟨_, colLoop_out store (fun a r h => hc a r (hC _ _ _ h)) hwl hp hb⟩

/-- **`da_verify`, soundly**: on a valid execution's memory and the squares table, the returned
cells are a root and a vector digest that some LeanDA witness opens (`da_verify_sound_w`, its
column loops' witness functions chosen). -/
theorem da_verify_sound {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq) {r0 r1 v0 v1 : E}
    (h : coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧
      w.Opens root vd := by
  rw [rel_of_find find_dv] at h
  obtain ⟨σ, hp, hb⟩ := h
  obtain ⟨w90, h90⟩ := exists_witFn (colsOut_exists true (rd := rd))
  obtain ⟨w91, h91⟩ := exists_witFn (colsOut_exists false (rd := rd))
  obtain ⟨root, vd, e1, e2, ho⟩ := daOut_iff.mp (da_verify_sound_w (fun _ _ _ h => h) hm hT h90 h91 hp hb)
  exact ⟨root, vd, _, e1, e2, ho⟩

/-! ## The dispatch bounds group K's checker assumes -/

/-- `da_row_shape`'s argument `1` is `g^k`, `k < 11` (its post `(3, 11)`): `da_verify`'s dispatch
on it, and the columns' (`da_verify_column`'s argument `4`), stay in their tables. -/
theorem da_row_shape_glp_lt {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {n_blob glp : E} {rets : List E} (h : coreProgram.Rel rd "da_row_shape" [n_blob, glp, gsq] rets) :
    ∃ k < 11, glp = gen ^ k := by
  obtain ⟨_, _, _, _, _, ha, -, r, -, hr2, -, hglp, -⟩ := (da_row_shape_iff hm hT _ _ _).mp h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨-, rfl, -⟩ := ha
  exact ⟨_, by have := logPad_le hr2; omega, hglp⟩

/-- `da_list_digest`'s argument `1` is `g^k`, `k < 17`. -/
theorem da_list_digest_ng_lt {rd : Reader} {roots n_g : E} {rets : List E}
    (h : coreProgram.Rel rd "da_list_digest" [roots, n_g] rets) : ∃ k < 17, n_g = gen ^ k := by
  obtain ⟨_, _, _, _, ha, -, claims, hlen, hng, -⟩ := (da_list_digest_iff rd _ _).mp h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨-, rfl⟩ := ha
  exact ⟨_, by omega, hng⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (DaFacts da_verify_facts daFacts_opens da_verify_sound daWitOf daWitOf_congr opens_of
  DaOut daOut_iff dvCol dvWit da_verify_sound_w da_row_shape_glp_lt
  da_list_digest_ng_lt)
end LeanVM.Guest.B1
