/-
  LeanVM.Guest.EndCompleteCT

  The completeness end theorem's pieces under a semantics over an answered hash, `main`'s tree
  kept (`EndCompleteC.lean` with tree predicates): `main`'s completeness giving trees satisfying
  `MainQ`, the honest tree the retemped one of such a tree.
-/

module

public import LeanVM.Guest.EndCompleteC
public import LeanVM.Guest.B1.Main.MainCompleteT
public import LeanVM.Guest.B1.Main.MainBudgetC

/-!
# Completeness under a semantics, the tree kept

* `MainCompleteCT S Ha Ht fs cert cnt b VsQ vr`: `MainCompleteC`, `main`'s tree also satisfying
  `MainQ VsQ (vr seed s w)` at `main`'s honest valuation;
* `mainCompleteC_ofT`: `mainCompleteC_of` with `verify_sub` complete by trees satisfying `VsQ`
  (`HV`) and the children's runs `vr`;
* `honest_of_mainCT`: `honest_of_mainC`, the honest tree being the retemped one of a tree
  satisfying `MainQ` on the memory of `main`'s layouts.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1 (LowDef CompleteAtWST)
open LeanVM.Guest.B1.Main (imageOf LConsistent Layout MemL KFacts MainQ mainVal mainRunAt honestWordsC)

@[expose] public section

variable (S : BlakeSem) (Ha : List UInt8 → Option Digest) (Ht : List UInt8 → Digest)
  (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget)
  (VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop)
  (vr : Digest → NodeStatement → NodeWitness → ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC)

/-- **`main`'s completeness, its tree kept** (`MainCompleteC`): `main`'s tree also satisfies `MainQ`
at the children's runs `vr seed s w` and `main`'s honest valuation on the memory. -/
def MainCompleteCT : Prop :=
  ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
    NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
    Limits s w → E2E.Complete.CapsAgreeWith Ht seed w → b.size (work s w) ≤ 2 ^ 28 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 32 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef 16 rd → MemL rd L → rd 1 = some (hdrOf pi).1 → rd g = some (hdrOf pi).2 →
        ∃ t : Tree, t.name = "main" ∧ t.ValidB S coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
          t.Placed coreProgram fs cert 0 ∧ t.total fs = N ∧
          t.LoadsIn coreProgram fs cert (fun i => i < 2) 0 ∧
          (∀ op, cnt t op ≤ (b.instrs op).eval (work s w)) ∧
          MainQ VsQ (vr seed s w) fs w.children.length 0
            (mainVal rd (mainRunAt fs 0 (honestWordsC Ht seed s w))) rd t

variable {S Ha Ht fs cert cnt b VsQ vr}

/-- `MainCompleteCT` forgets its trees' predicate. -/
theorem MainCompleteCT.toC (h : MainCompleteCT S Ha Ht fs cert cnt b VsQ vr) :
    MainCompleteC S Ha Ht fs cert cnt b := by
  intro seed s w pi hpi hrel hlim hcap hbs
  obtain ⟨N, L, h1, h2, h3, h4, h5⟩ := h seed s w pi hpi hrel hlim hcap hbs
  refine ⟨N, L, h1, h2, h3, h4, fun rd hl hL h0 h1 => ?_⟩
  obtain ⟨t, a, b', c, d, e, f, g, -⟩ := h5 rd hl hL h0 h1
  exact ⟨t, a, b', c, d, e, f, g⟩

/-- **The `honest` piece, the tree kept** (`honest_of_mainC`): the honest tree is `T0`'s retemped
one, `T0` satisfying `MainQ` on the memory `rd0` of `main`'s layouts. -/
theorem honest_of_mainCT {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)}
    (hm : MainCompleteCT S Ha Ht fs cert cnt b VsQ vr) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
      NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
      Limits s w → E2E.Complete.CapsAgreeWith Ht seed w → b.size (work s w) ≤ 2 ^ 28 →
      ∃ (rd0 : Reader) (T0 : Tree) (ν : ℕ → String → Val → V → E), T0.name = "main" ∧
        T0.ValidB S coreProgram rd0 [] [] ∧
        MainQ VsQ (vr seed s w) fs w.children.length 0
          (mainVal rd0 (mainRunAt fs 0 (honestWordsC Ht seed s w))) rd0 T0 ∧
        HonestAtB S coreProgram fs H C (hdrOf pi) (T0.retemp coreProgram fs ν 0) cert
          (honest coreProgram fs H C (hdrOf pi) (T0.retemp coreProgram fs ν 0)).read [] [] ∧
        (T0.retemp coreProgram fs ν 0).total fs ≤ b.words.eval (work s w) ∧
        ∀ op, cnt (T0.retemp coreProgram fs ν 0) op ≤ (b.instrs op).eval (work s w) := by
  intro seed s w pi hpi hrel hlim hcap hbs
  obtain ⟨N, L, hcons, hin, hN, hNb, hrelL⟩ := hm seed s w pi hpi hrel hlim hcap hbs
  set hdr := hdrOf pi with hhdr
  have h16 : 16 ≤ logMem N := minLogMem_le_logMem N
  have h64 : logMem N < 64 := by have := logMem_le_maxLogMem hN; unfold maxLogMem at this; omega
  set M := imageOf (logMem N) L hdr with hM
  have hlow : LowDef 16 M.read := fun i hi => by
    have hi' : i < 2 ^ logMem N :=
      lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) h16)
    rw [MemImage.read_gpow h64 M ⟨i, hi'⟩]; rfl
  have hL := B1.Main.memL_imageOf h64 hcons (fun q hq => ⟨(hin q hq).1,
    le_trans (hin q hq).2 (le_two_pow_logMem N)⟩) hdr
  obtain ⟨hh0, hh1⟩ := B1.Main.imageOf_hdr h64 (by omega) L hdr
  have e0 : (1 : K) = Parameters.gpow 0 := by simp [Parameters.gpow]
  have e1 : g = Parameters.gpow 1 := by simp [Parameters.gpow]
  obtain ⟨t, hn, hv, hb, hp, ht, hl, hcntT, hQ⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
    (by rw [e1]; exact hh1)
  subst ht
  have hkf := hk hdr t hn
  have hd : DischargeHypsB S coreProgram fs cert H C hdr t (fun i => i < 2) M [] [] :=
    { fresh := coreProgram_fresh
      valid := hv
      bufsOk := hb
      placed := hp
      loads := hl
      region := fun i hi => Or.inl hi
      hdr_read := ⟨hh0, hh1⟩
      size := hN
      addr := B1.Main.dischargeAddrS h64 hv hp fun I hI f σ bufs kids hIt p r rs ha k hk' => by
        have hcl := (hkf.run I hI f σ bufs kids hIt p r rs ha k hk').1
        have hoff := (hkf.cells.off I hI _ hcl).2
        have hw := honest_within (P := coreProgram) hI (by have := hkf.cells.two_le I hI; omega)
        have := le_two_pow_logMem (t.total fs)
        omega
      cells := hkf.cells
      cells' := hkf.cells'
      cert_lt := hkf.cert_lt
      cert_inj := hkf.cert_inj
      run := hkf.run
      tmp := hkf.tmp
      keep := hkf.keep }
  obtain ⟨ν, hν⟩ := honestAtB_retemp hd
  refine ⟨M.read, t, ν, hn, hv, hQ, hν, by rw [total_retemp]; exact hNb, fun op => ?_⟩
  rw [hc]
  exact hcntT op

/-- **`main` is complete within the budget, its tree kept** (`mainCompleteC_of`): `verify_sub`
complete by trees satisfying `VsQ` at every good run (`HV`), each child run by `vr seed s w c`. -/
theorem mainCompleteC_ofT (hag : ∀ x d, Ha x = some d → d = Ht x) (fs : String → ℕ)
    (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget)
    {VsGood : B1.VerifySub.VsData → B1.VerifySub.VsRunC → Prop} {Bd : B1.Main.CalleeBounds}
    (H : B1.Main.CalleesAtC Ha S fs cert 16 VsGood Bd) (hF : B1.Main.FsRowsC S Ha)
    (hBs : B1.Main.BsRowsC S Ha) (ω : Opcode → String → ℕ) (Wt : ∀ op, B1.Main.MainWeightHypsS S fs (ω op))
    (jt : Opcode → ℕ) (hfs : 2 ≤ fs "main")
    (VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop)
    (HV : ∀ D R, VsGood D R → ∀ lpA sqA outA : ℕ, ∀ (c : Opcode → B1.VerifySub.VsStat),
      (∀ θ, B1.VerifySub.VsStatOkS S (ω θ) (c θ)) →
      CompleteAtWST S fs cert ω 16 "verify_sub" (B1.Main.vsExtLR lpA sqA outA D R)
        [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
          (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
          ofK (Parameters.gpow outA)] (B1.Returns []) Bd.vs (fun θ => Bd.vsW (ω θ) (c θ)) (VsQ D R))
    (vr : Digest → NodeStatement → NodeWitness → ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC)
    (hacc : ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
      NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
      Limits s w → E2E.Complete.CapsAgreeWith Ht seed w →
      (∀ c ∈ w.children, B1.Main.FreshShaped c.fresh) ∧ ∀ c (hc : c < w.children.length),
        VsGood (vr seed s w c).1 (vr seed s w c).2 ∧
        (vr seed s w c).1.pi = B1.Main.statementDigestH Ht seed w.children[c].statement ∧
        (vr seed s w c).1.seed = seed ∧
        (vr seed s w c).2.fresh (vr seed s w c).1 = w.children[c].fresh)
    (hwords : ∀ seed s w, NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
      Limits s w → B1.Main.mainBound fs Bd (honestWordsC Ht seed s w) ≤ b.words.eval (work s w))
    (hcnt : ∀ (rd : Reader) (t : Tree), t.ValidB S coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op)
    (hinstrs : ∀ seed s w, NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
      Limits s w → ∀ op,
      B1.Main.mainWeightS S (ω op) Bd (Wt op) (honestWordsC Ht seed s w) + jt op ≤ (b.instrs op).eval (work s w)) :
    MainCompleteCT S Ha Ht fs cert cnt b VsQ vr := by
  intro seed s w pi hpi hN hlim hcaps hbs
  have hc := hacc seed s w pi hpi hN hlim hcaps
  obtain ⟨m, L, hW, hD, hmB, hrel⟩ := B1.Main.mainC_completeWT fs Ht H hF hBs hag Wt le_rfl
    bytecode_length hN hpi hlim hc.1 VsQ HV (vr seed s w) hc.2 0
  rw [Nat.zero_add] at hW
  have hbw := hwords seed s w hN hlim
  have hb32 : b.words.eval (work s w) ≤ 2 ^ 32 := le_trans (words_le_of_size hbs) (by norm_num)
  have hin : ∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ fs "main" + m := fun q hq => by
    have := hW q hq; omega
  refine ⟨fs "main" + m, L, B1.Main.lConsistent_of_pairwise hD, hin, le_trans (le_trans hmB hbw) hb32,
    le_trans hmB hbw, fun rd hl hL h0 h1 => ?_⟩
  obtain ⟨t, hq, hn, hv, hb, hp, ht, hl', -, hw⟩ := hrel rd hl hL h0 h1
  exact ⟨t, hn, hv, hb, hp, ht, hl', fun op =>
    le_trans (hcnt rd t hv op) (le_trans (Nat.add_le_add_right (hw op) _) (hinstrs seed s w hN hlim op)),
    hq⟩

end
end LeanVM.Guest.End
