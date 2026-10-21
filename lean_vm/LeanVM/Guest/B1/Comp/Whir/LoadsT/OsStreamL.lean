/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsStreamL

  Every valid tree of an `open_stacked` specialization loads the stream words it reads; adding a
  property of every valid tree to a `CompleteAtBST`.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsLen
public import LeanVM.Guest.B1.Comp.VerifySub.PlacedEqKids
public import LeanVM.Guest.B1.Comp.TreeRoot

/-!
# `open_stacked` loads its stream

* `osL_ctx`: a node of a straight-line body holds its `OsLdCtx` with its own load equations;
* `os_streamLoads`: every valid tree of `openName μ r` on the reads' arguments, the cursor
  `g^c`, loads the `osStreamLen` stream words at `g^c` (`LoadsWords`);
* `CompleteAtBST.and_of_valid`: a property every valid tree of `f` has joins a `CompleteAtBST`'s.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Located LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- **A node of a straight-line body holds its `OsLdCtx`**, its loads its own load equations. -/
theorem osL_ctx {S : BlakeSem} {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (hw : walk σ fn.body = .ret (pre.flatMap (Main.slEvs σ)) vs)
    (hes : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ)
    (hk : Tree.KidsValidB S coreProgram rd σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) kids) :
    OsLdCtx S rd σ pre ((Memory.Tree.node f σ bufs kids).loadEqns coreProgram) where
  atoms a ha := hes _ (mem_slEvs_of ha)
  loads d p off hm := mem_loadEqns_node hf hw (mem_evLoadEqns (mem_slEvs_of hm))
  calls g args rets hm := by
    have hc : (⟨g, args, rets, true⟩ : Call) ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ) :=
      List.mem_map.mpr ⟨(none, g, args, rets), List.mem_filterMap.mpr ⟨_, hm, rfl⟩, rfl⟩
    obtain ⟨k, hk', hn, hv⟩ := osL_kidOf hk _ hc rfl
    exact ⟨k, hn, hv, fun q hq => mem_loadEqns_kid hk' hq⟩

/-- **Every valid tree of a function with body `osBody cfg` loads its stream**: on arguments whose
sixth, the stream's cursor, is `g^c`, the `osStreamLen cfg` words at `g^c` it reads. -/
theorem os_streamLoadsCfg {S : BlakeSem} {cfg : OsCfg} {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5])
    (hbody : fn.body = osBody cfg) (hbf : OsBodyFacts cfg) (hfm : OsFmOk cfg)
    (hlq : osStreamLen cfg = 2 + osLvsCntL cfg 0 cfg.levels + 2 * (cfg.yrLog - 1))
    (hlb : osStreamLen cfg < 2 ^ 64) {rd : Reader} {c : ℕ} {xs : List E}
    {args rets : List E} {t : Tree} (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hlen : xs.length = osStreamLen cfg) (hc : args.getD 5 0 = ofK (Parameters.gpow c))
    (hn : t.name = name) (hv : t.ValidB S coreProgram rd args rets) :
    LoadsWords t c xs := by
  have hread := osL_validB_read t hv
  have hb : fn.body = (osBody cfg).dropLast ++ [.ret (osRetVs cfg)] := by rw [hbody]; exact hbf.last
  have hst := hbf.straight
  have hsub : OsSub ((osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++
      (osTail cfg.yrLog (OsRun.sL cfg)).1 ++ osFinPre cfg) (osBody cfg).dropLast := by
    rw [os_pre_eq]; exact fun _ h => h
  generalize (osBody cfg).dropLast = pre at hb hst hsub
  obtain ⟨σ, bufs, kids, rfl, hp, hw, -, hes, hk⟩ := osL_node (S := S) hf hb hst hn hv
  have X := osL_ctx (bufs := bufs) hf hw hes hk
  have h5 : σ (.n 5) = ofK (Parameters.gpow c) := by
    rw [← hc, ← hp, hpar]; rfl
  obtain ⟨c0, r0⟩ := osL_head X hsub.left.left.left h5
  obtain ⟨c1, r1⟩ := osL_levels X cfg 0 cfg.levels _ 2 (fun _ _ _ => hfm)
    hsub.left.left.right c0 (by omega)
  have r2 := osL_tail X (s := OsRun.sL cfg) hsub.left.right c1 (by omega)
  have hall : OsRdL _ c 0 (osStreamLen cfg) :=
    (r0.cat r1 rfl rfl).cat r2 (by omega) (by omega)
  intro k hk
  obtain ⟨v, hv'⟩ := hall k (by omega)
  rw [Nat.zero_add] at hv'
  have h1 := hread _ hv'
  have h2 := (hx k hk).2
  rw [Main.addr_ofK] at h2
  rw [h1] at h2
  rwa [← Option.some.inj h2]

/-- **`os_streamLoadsCfg` at the specialization `j`.** -/
theorem os_streamLoadsA {S : BlakeSem} {j : ℕ} (hj : j < 28) {rd : Reader} {c : ℕ} {xs : List E}
    {args rets : List E} {t : Tree} (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hlen : xs.length = osStreamLen (osCfgs.getD j default)) (hc : args.getD 5 0 = ofK (Parameters.gpow c))
    (hn : t.name = openNames.getD j "") (hv : t.ValidB S coreProgram rd args rets) :
    LoadsWords t c xs := by
  obtain ⟨⟨fn, hf, hpar, hbody⟩, -, -⟩ := os_inst j hj
  obtain ⟨hlq, hlb⟩ := osStreamLen_eq j hj
  exact os_streamLoadsCfg hf hpar hbody (osL_bodyFacts j hj) (osL_fmOk j hj) hlq hlb hx hlen hc hn hv

/-- **`os_streamLoadsA` at `openName μ r`** on `open_stacked`'s arguments. -/
theorem os_streamLoads {S : BlakeSem} {μ r : ℕ} (h22 : 22 ≤ μ) (h28 : μ ≤ 28) (h1 : 1 ≤ r) (h4 : r ≤ 4)
    {rd : Reader} {c : ℕ} {xs : List E} {cv root : Digest} {target : E} {rets : List E} {t : Tree}
    (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hlen : xs.length = osStreamLen (osCfgOf (openName μ r))) (hn : t.name = openName μ r)
    (hv : t.ValidB S coreProgram rd [(digestScalars cv).1, (digestScalars cv).2, target,
      (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)] rets) :
    LoadsWords t c xs := by
  have hj : μ - 22 + 7 * (r - 1) < 28 := by omega
  have hcfg : osCfgOf (openName μ r) = osCfgs.getD (μ - 22 + 7 * (r - 1)) default := by
    rw [osCfgOf, openName, openNames_idxOf _ hj]
  rw [hcfg] at hlen
  exact os_streamLoadsA hj hx hlen rfl hn hv

/-- **A property of every valid tree of `f` joins a `CompleteAtBST`'s.** -/
theorem CompleteAtBST.and_of_valid {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}
    {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ}
    {Q Q' : ℕ → Reader → Tree → Prop} (h : CompleteAtBST S fs cert κ f Lin args Out B Q)
    (hQ' : ∀ fp rd, LowDef κ rd → MemL rd Lin → ∀ t rets, t.name = f →
      t.ValidB S coreProgram rd args rets → Q' fp rd t) :
    CompleteAtBST S fs cert κ f Lin args Out B (fun fp rd t => Q' fp rd t ∧ Q fp rd t) := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, hO, hW, hD, hB, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, hO, hW, hD, hB, fun rd hk hm => ?_⟩
  obtain ⟨t, hq, hn, hv, rest⟩ := hR rd hk hm
  exact ⟨t, ⟨hQ' fp rd hk (memL_append.mp hm).2 t rets hn hv, hq⟩, hn, hv, rest⟩

end
end LeanVM.Guest.B1
