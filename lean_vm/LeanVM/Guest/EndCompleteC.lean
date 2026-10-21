/-
  LeanVM.Guest.EndCompleteC

  The completeness end theorem's pieces under a semantics `S` over an answered hash: `main`'s
  completeness over the hash (`MainCompleteC`), the honest tree from it, and the valid execution
  and its committed size under `S` from an honest tree within the budget.
-/

module

public import LeanVM.E2E.Complete.Interfaces
public import LeanVM.Guest.B1.Main.HonestPieceS
public import LeanVM.Guest.B2C.B2FinalB
public import LeanVM.Guest.B2C.TableB
public import LeanVM.Guest.B2C.CountsMeet

/-!
# Completeness under a semantics, the end

`EndComplete.lean` and `End.lean`'s completeness under `S : BlakeSem` over an answered hash `Ha`
(a total `Ht` agreeing with it where it answers, for the caps):

* `MainCompleteC S Ha Ht fs cert cnt b`: `MainComplete` with `NodeRelWith Ha` from the guest's
  baked start and padding, the statement's digest the answered `pi`, the caps agreeing under `Ht`,
  the tree valid under `S`;
* `honest_of_mainC`: the `honest` piece under `S` (`honest_of_main`, by `honestAtB_retemp`);
* `validB_of_honestC`: from an honest tree of `main` under a functional `S` at the deployed frame
  sizes, certificates, headers and cells, within words `W` and counts `I` whose size is within
  `2^28`, a valid execution under `S` on the public input of `pi`, of committed size under `S` at
  most `2^28` (`guest_complete_of` under `S`: the jump table's prologue `runCB_jumpTables`, B2's
  `b2cB2B` and `b2cCountB`, the counts meeting by `B2C.countB_eq`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (imageOf LConsistent Layout MemL KFacts)

@[expose] public section

variable (S : BlakeSem) (Ha : List UInt8 → Option Digest) (Ht : List UInt8 → Digest)
  (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget)

/-- **`main`'s completeness within the budget under `S` over the answered hash `Ha`**
(`MainComplete`): for a node relation with every hash answered by `Ha` from the guest's baked
start and padding, the statement's digest answered `pi`, within the limits and the caps agreeing
under `Ht`, the budget's size within `2^28`: a consistent layout of `N` words, `N` within the
budget, on every memory holding which with `pi` as its header `main` holds under `S` by a tree
placed at `0`, of `N` words, loading from its own data or its header, within the budget's
instruction counts. -/
def MainCompleteC : Prop :=
  ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
    NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
    Limits s w → E2E.Complete.CapsAgreeWith Ht seed w → b.size (work s w) ≤ 2 ^ 28 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 32 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef 16 rd → MemL rd L → rd 1 = some (hdrOf pi).1 → rd g = some (hdrOf pi).2 →
        ∃ t : Tree, t.name = "main" ∧ t.ValidB S coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
          t.Placed coreProgram fs cert 0 ∧ t.total fs = N ∧
          t.LoadsIn coreProgram fs cert (fun i => i < 2) 0 ∧
          ∀ op, cnt t op ≤ (b.instrs op).eval (work s w)

variable {S Ha Ht fs cert cnt b}

/-- **The `honest` piece under `S`**, from `main`'s completeness over the hash, the certificate's
facts and the counts' invariance (`honest_of_main`). -/
theorem honest_of_mainC {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)}
    (hm : MainCompleteC S Ha Ht fs cert cnt b) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
      NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bytecode seed s w →
      Limits s w → E2E.Complete.CapsAgreeWith Ht seed w → b.size (work s w) ≤ 2 ^ 28 →
      ∃ (rd : Reader) (T : Tree), T.name = "main" ∧
        HonestAtB S coreProgram fs H C (hdrOf pi) T cert rd [] [] ∧
        T.total fs ≤ b.words.eval (work s w) ∧ ∀ op, cnt T op ≤ (b.instrs op).eval (work s w) := by
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
  obtain ⟨t, hn, hv, hb, hp, ht, hl, hcntT⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
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
  refine ⟨_, _, by rw [name_retemp]; exact hn, hν, by rw [total_retemp]; exact hNb, fun op => ?_⟩
  rw [hc]
  exact hcntT op

/-- The committed size under `S` of a run on `2^logMem n` words is `sizeOf n` at its counts
under `S` (`committedSize_eq`). -/
theorem committedSizeB_eq {n : ℕ} (L : MemImage (logMem n)) (steps : ℕ) :
    (⟨_, L, steps⟩ : Trace guest).committedSizeB S =
      sizeOf n (fun op => (⟨_, L, steps⟩ : Trace guest).countB S op) :=
  rfl

/-- **A valid execution under `S` from an honest tree within the budget** (`guest_complete_of`
under `S`): on the honest memory at the deployed frame sizes, certificates, headers and cells,
`main`'s tree within the words `W` and the counts `I`, its run under a functional `S` is a valid
execution on the public input of `pi`, of committed size under `S` at most `sizeOf W I`. -/
theorem validB_of_honestC (hfun : B2C.SemFunctional S) {pi : Digest} {rd : Reader} {T : Tree}
    (hn : T.name = "main")
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C (hdrOf pi) T B2C.cert rd [] [])
    {W : ℕ} {I : Opcode → ℕ} (hw : T.total B2C.fs ≤ W) (hc : ∀ op, B2C.cnt T op ≤ I op) :
    ∃ n, ValidExecutionB S guest (publicInputOf pi)
        ⟨_, honest coreProgram B2C.fs B2C.H B2C.C (hdrOf pi) T, n⟩ ∧
      (⟨_, honest coreProgram B2C.fs B2C.H B2C.C (hdrOf pi) T, n⟩ : Trace guest).committedSizeB S ≤
        sizeOf W I := by
  have hb := hH.toHonestB.publicBoundary (prog := guest)
  have hjt := B2C.jumpTablesB_honestC hH.toHonestB hn
  have hreach := (B2C.runCB_jumpTables hjt).reach.trans (B2C.b2cB2B hfun _ rd T hn hH)
  obtain ⟨n, hv⟩ := validExecutionB_of_reach hb hreach
  refine ⟨n, hv, ?_⟩
  rw [committedSizeB_eq]
  refine sizeOf_mono hw fun op => le_trans ?_ (hc op)
  rw [B2C.countB_eq]
  exact B2C.b2cCountB hfun _ rd T hn hH n hv.2 op

end
end LeanVM.Guest.End
