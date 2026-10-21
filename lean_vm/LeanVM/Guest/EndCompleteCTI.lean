/-
  LeanVM.Guest.EndCompleteCTI

  `honest_of_mainCT` with the honest memory's words: each `0`, the layouts' memory's, or in a frame.
-/

module

public import LeanVM.Guest.EndCompleteCT

/-!
# The honest memory's words

`honest_of_mainCT'`: `honest_of_mainCT`, the memory `rd0` of `main`'s layouts (on which `T0` is
valid) holding `main`'s own (`mainIn`), and every word the honest memory of the re-chosen tree
holds is `0`, `rd0`'s, or in a frame of one of `T0`'s instances (`honestAtB_retemp_F`). A decoder reading a `HeapBuf` cell thus
reads the layouts' word there or `0`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1 (LowDef CompleteAtWST)
open LeanVM.Guest.B1.Main (imageOf LConsistent Layout MemL KFacts MainQ mainVal mainRunAt honestWordsC)

@[expose] public section

variable {S : BlakeSem} {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest}
  {fs : String → ℕ} {cert : String → V → ℕ} {cnt : Tree → Opcode → ℕ} {b : Budget}
  {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Tree → Prop}
  {vr : Digest → NodeStatement → NodeWitness → ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC}
  {CQ : List E → List E → ℕ → Reader → Tree → Prop}
  {SQ : List E → List E → ℕ → Reader → Tree → Prop} {LQ : List E → ℕ → Reader → Tree → Prop}

/-- **The `honest` piece, the tree and the words kept** (`honest_of_mainCT`): also every word of
the honest memory is `0`, `rd0`'s, or in a frame of an instance of `T0`. -/
theorem honest_of_mainCT' {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)}
    (hm : MainCompleteCT S Ha Ht fs cert cnt b VsQ vr CQ SQ LQ) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
      NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
      Limits s w → E2E.Complete.CapsAgreeWith Ht seed w → b.size (work s w) ≤ 2 ^ 28 →
      ∃ (rd0 : Reader) (T0 : Tree) (ν : ℕ → String → Val → V → E), T0.name = "main" ∧
        T0.ValidB S coreProgram rd0 [] [] ∧
        MainQ VsQ (vr seed s w) CQ SQ LQ (B1.Main.mainIQ fs 0 (honestWordsC Ht seed s w)) fs w.children.length 0
          (mainVal rd0 (mainRunAt fs 0 (honestWordsC Ht seed s w))) rd0 T0 ∧
        HonestAtB S coreProgram fs H C (hdrOf pi) (T0.retemp coreProgram fs ν 0) cert
          (honest coreProgram fs H C (hdrOf pi) (T0.retemp coreProgram fs ν 0)).read [] [] ∧
        (T0.retemp coreProgram fs ν 0).total fs ≤ b.words.eval (work s w) ∧
        (∀ op, cnt (T0.retemp coreProgram fs ν 0) op ≤ (b.instrs op).eval (work s w)) ∧
        MemL rd0 (B1.Main.mainIn fs 0 (honestWordsC Ht seed s w)) ∧
        ∀ (a : K) (x : E), (honest coreProgram fs H C (hdrOf pi) (T0.retemp coreProgram fs ν 0)).read a =
            some x →
          x = 0 ∨ rd0 a = some x ∨
            ∃ I ∈ honestInsts coreProgram fs H (hdrOf pi) T0, ∃ i, I.Frame fs i ∧ a = gpow i := by
  intro seed s w pi hpi hrel hlim hcap hbs
  obtain ⟨N, L, hcons, hin, hN, hNb, hsub, hrelL⟩ := hm seed s w pi hpi hrel hlim hcap hbs
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
  obtain ⟨ν, hν, himg⟩ := honestAtB_retemp_F hd
  refine ⟨M.read, t, ν, hn, hv, hQ, hν, by rw [total_retemp]; exact hNb, fun op => ?_, hsub.1 _ hL,
    himg⟩
  rw [hc]
  exact hcntT op

end
end LeanVM.Guest.End
