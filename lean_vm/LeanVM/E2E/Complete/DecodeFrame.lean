/-
  LeanVM.E2E.Complete.DecodeFrame

  `main`'s frame on the honest memory, as the decoder reads it: the regions' sizes, the coverage
  table's length, the tables' pointers, and the running counts.
-/

module

public import LeanVM.E2E.Complete.DecodeVsArgs
public import LeanVM.E2E.Complete.DecodeStmt

/-!
# `main`'s frame, decoded

The decoder reads the children's statements (`B1.Main.kidStmt`) at `main`'s frame
(`B1.Main.frameOf (mainFrame L)`): the running counts' table `written` (value `145`), the leanXMSS
and leanSPHINCS tables (`77`, `80`), the coverage table (`103`) and its DA region (`104`), the DA
roots (`69`), the carried claims (`142`), the regions' sizes (`55`, `56`, `50`, as logs) and the
coverage table's length (`58`). On the honest memory of `main`'s re-chosen tree at `main`'s honest
valuation over the honest words `honestWordsC`, each is the honest one (`mainFrame_words`): every
one of these values is named by `main`'s prologue and middle at a cell of its frame
(`frameVals_named`), so `main`'s frame reads it (`mainFrame_eqN`), and `main`'s valuation holds the
honest words there (`mainVal_frameWords`). `countOf_honest`: the running counts, read through
`written`, are the honest writers' numbers `hbase`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B2C (cellJ fsN)
open LeanVM.Guest.B1.Main (honestWordsC hbase planX planS planD mainPtr mainVal mainRunAt gLog
  frameOf countOf cellAt)

@[expose] public section

/-- The values of `main`'s frame the decoder's `frameOf` and `kidStmt` read. -/
def frameVals : List V :=
  [.n 145, .n 77, .n 80, .n 103, .n 69, .n 104, .n 142, .n 55, .n 56, .n 50, .n 58]

set_option maxRecDepth 100000 in
/-- Each is named by `main`'s prologue and middle, at a cell of its frame, and used by its body. -/
theorem frameVals_named : frameVals.all (fun v => decide (v ∈ mainNamedUses) && Nat.ble 2 (cellJ 1 v) &&
    Nat.blt (cellJ 1 v) (fsN 1) && decide (v ∈ Stmt.usesList (Fn.body Data.core0))) = true := by
  decide +kernel

/-- `main`'s honest words at the values of its frame the decoder reads. -/
theorem mainVal_frameWords (fs : String → ℕ) (rd : Reader) (fp : ℕ) (W : B1.Main.MainWords) :
    [145, 77, 80, 103, 69, 104, 142, 55, 56, 50, 58].map
      (fun i => mainVal rd (mainRunAt fs fp W) (.n i)) =
      [mainPtr fs fp W 8, mainPtr fs fp W 1, mainPtr fs fp W 2, mainPtr fs fp W 4, mainPtr fs fp W 0,
        mainPtr fs fp W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)), mainPtr fs fp W 7,
        gen ^ W.dx * gen ^ W.ux, gen ^ W.ds * gen ^ W.us, gen ^ W.da * gen ^ W.ud,
        gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us) * (gen ^ W.da * gen ^ W.ud)] := by
  simp only [List.map_cons, List.map_nil, mainVal, mainRunAt]
  b1_look

/-- **`main`'s frame on the honest memory, as the decoder reads it**: on the honest memory of
`main`'s re-chosen tree whose root valuation is `main`'s honest valuation over `honestWordsC`, the
regions' sizes, the coverage table's length (`58`), the DA region's pointer, and the tables'
pointers are the honest ones. -/
theorem mainFrame_words {S : BlakeSem} (hB : B2C.B2HypsB S) {hdr : E × E} {rd rd0 : Reader}
    {T0 : Tree} {ν : ℕ → String → Val → V → E} {σ0 : Val} {bufs : List ℕ} {ks : List Tree}
    (hT0 : T0 = .node "main" σ0 bufs ks)
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      rd [] [])
    {Ht : List UInt8 → Digest} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hlim : End.Limits s w)
    (hσ0 : σ0 = mainVal rd0 (mainRunAt B2C.fs 0 (honestWordsC Ht seed s w))) :
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).Lx = s.claims.xmss.length + (planX s w).2.length ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).Ls = s.claims.sphincs.length + (planS s w).2.length ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).Md = s.claims.da.length + (planD s w).2.length ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).daC =
      (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).cover *
        gen ^ (s.claims.xmss.length + (planX s w).2.length +
          (s.claims.sphincs.length + (planS s w).2.length)) ∧
    gLog (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0))
        (.n 58)) =
      s.claims.xmss.length + (planX s w).2.length + (s.claims.sphincs.length + (planS s w).2.length) +
        (s.claims.da.length + (planD s w).2.length) ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).cover = mainPtr B2C.fs 0 (honestWordsC Ht seed s w) 4 ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).lxT = mainPtr B2C.fs 0 (honestWordsC Ht seed s w) 1 ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).spT = mainPtr B2C.fs 0 (honestWordsC Ht seed s w) 2 ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).daR = mainPtr B2C.fs 0 (honestWordsC Ht seed s w) 0 ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).carried = mainPtr B2C.fs 0 (honestWordsC Ht seed s w) 7 ∧
    (frameOf (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
        (T0.retemp coreProgram B2C.fs ν 0)))).written =
      mainPtr B2C.fs 0 (honestWordsC Ht seed s w) 8 := by
  set T := T0.retemp coreProgram B2C.fs ν 0 with hT
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  set W := honestWordsC Ht seed s w with hW
  have hTn : T = .node "main" (retempVal coreProgram ν 0 "main" σ0) bufs
      (Memory.Tree.retempKids coreProgram B2C.fs ν (kidPos B2C.fs coreProgram.loop 0 "main" bufs
        (ks.map (Memory.Tree.total B2C.fs))) ks) := by
    rw [hT, hT0, retemp_node]
  have hname : T.name = "main" := by rw [hTn]; rfl
  -- `main`'s frame at the values the decoder reads
  have hok := List.all_eq_true.mp frameVals_named
  have key : ∀ v ∈ frameVals, mainFrame L v = mainVal rd0 (mainRunAt B2C.fs 0 W) v := by
    intro v hv
    have h := hok v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨hn, h2⟩, h3⟩, hu⟩ := h
    rw [mainFrame_eqN hB hname hH hTn hn h2 h3, retempVal_uses coreProgram_fresh B1.Main.find_main hu,
      hσ0]
  have hmv := mainVal_frameWords B2C.fs rd0 0 W
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmv
  obtain ⟨m145, m77, m80, m103, m69, m104, m142, m55, m56, m50, m58, -⟩ := hmv
  have f : ∀ i, V.n i ∈ frameVals → mainFrame L (.n i) = mainVal rd0 (mainRunAt B2C.fs 0 W) (.n i) :=
    fun i hi => key _ hi
  have f145 := f 145 (by simp [frameVals])
  have f77 := f 77 (by simp [frameVals])
  have f80 := f 80 (by simp [frameVals])
  have f103 := f 103 (by simp [frameVals])
  have f69 := f 69 (by simp [frameVals])
  have f104 := f 104 (by simp [frameVals])
  have f142 := f 142 (by simp [frameVals])
  have f55 := f 55 (by simp [frameVals])
  have f56 := f 56 (by simp [frameVals])
  have f50 := f 50 (by simp [frameVals])
  have f58 := f 58 (by simp [frameVals])
  -- the sizes are below `2^16`
  have hsum : s.claims.xmss.length + (planX s w).2.length + (s.claims.sphincs.length + (planS s w).2.length) +
      (s.claims.da.length + (planD s w).2.length) < 2 ^ 16 := by
    have h0 := B1.Main.honest_total (seed := seed) hlim
    simp only [B1.Main.MainWords.total, B1.Main.honestWords] at h0
    exact h0
  have hdx : W.dx = s.claims.xmss.length := rfl
  have hux : W.ux = (planX s w).2.length := rfl
  have hds : W.ds = s.claims.sphincs.length := rfl
  have hus : W.us = (planS s w).2.length := rfl
  have hda : W.da = s.claims.da.length := rfl
  have hud : W.ud = (planD s w).2.length := rfl
  simp only [frameOf]
  rw [f55, f56, f50, f58, f104, f103, f77, f80, f69, f142, f145, m55, m56, m50, m58, m104, m103, m77,
    m80, m69, m142, m145, hdx, hux, hds, hus, hda, hud]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [← pow_add]; exact B1.Main.gLog_gen_pow (by omega)
  · rw [← pow_add]; exact B1.Main.gLog_gen_pow (by omega)
  · rw [← pow_add]; exact B1.Main.gLog_gen_pow (by omega)
  · simp only [pow_add]
  · simp only [← pow_add]; exact B1.Main.gLog_gen_pow (by omega)

/-- **The running counts, read through `written`, are the honest writers' numbers**: when the
running counts' table holds `g^(hbase s w c)` at each `c ≤ n_children`. -/
theorem countOf_honest {κ : ℕ} {L : MemImage κ} {s : NodeStatement} {w : NodeWitness}
    (hlim : End.Limits s w)
    (hw : ∀ c ≤ w.children.length, L.read ((frameOf (mainFrame L)).written.limb 0 * Parameters.gpow c) =
      some (gen ^ hbase s w c)) :
    ∀ c ≤ w.children.length, countOf L.read (mainFrame L) c = hbase s w c := by
  intro c hc
  have hmono : ∀ k, hbase s w c ≤ hbase s w (c + k) := fun k => by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact ih.trans (B1.Main.hbase_mono _)
  have hle := hmono (w.children.length - c)
  rw [Nat.add_sub_cancel' hc] at hle
  have ht := B1.Main.honest_total (seed := default) hlim
  rw [← B1.Main.hbase_children (seed := default) hlim] at ht
  unfold countOf cellAt
  rw [show mainFrame L (.n 145) = (frameOf (mainFrame L)).written from rfl, hw c hc, Option.getD_some]
  exact B1.Main.gLog_gen_pow (by omega)

end
end LeanVM.E2E.Complete
