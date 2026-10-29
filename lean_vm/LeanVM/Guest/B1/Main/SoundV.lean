/-
  LeanVM.Guest.B1.Main.SoundV

  `main`, soundly, its witness decoded from the frame map (the witness convention of G6,
  2026-10-23): every witness a function of a valuation, the memory and the frame map.
-/

module

public import LeanVM.Guest.B1.Main.Composed
public import LeanVM.Guest.B1.Da.VerifyW
public import LeanVM.Guest.B1.Sig.XmssSound
public import LeanVM.Guest.B1.Sig.SphincsSound

/-!
# `main`, its witness decoded from the frame map

`decWitV σ rd V piOf` is `decWit` with the callees' witness functions read off the frame map `V`:
a leanXMSS signature off its check's valuation (`Sig.xmssSigOf`), a leanSPHINCS one off its
check's with `main`'s byte table (`Sig.sphincsSigOf`), the DA matrix off `da_verify`'s and its
callees' (`Da.dvWit`), a child proof by `piOf` off `verify_sub`'s (B1-d), the batching's hints off
`aggregate_claims`' valuation and the memory (`aggHints`). It mentions no hash and no verifier.

`main_sound_V bytecode piOf` (G6's `MainSoundV bytecode (fun σ rd V ↦ decWitV σ rd V piOf)`):
under any call relation `C` that unfolds at `V` and lies below `coreProgram.Rel`, a run of
`main`'s body gives the statement of the public input's digest, held by `decWitV σ rd V piOf`.
`main_sound_V_of_sub`: it holds given `SubSoundW bytecode piOf`, `verify_sub`'s statement with its
proof named by `piOf` (the form B1-d's `verify_sub_sound_w_Spec` takes).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- **`main`'s witness, decoded from the frame map `V`.** -/
noncomputable def decWitV (σ : Val) (rd : Reader) (V : FrameMap)
    (piOf : Reader → Val → FrameMap → Proof) : NodeWitness :=
  decWit σ rd (fun p => Sig.xmssSigOf (V "verify_lean_xmss" [p] []))
    (fun p => Sig.sphincsSigOf (V "verify_sig_lean_sphincs" [p, σ (.n 68)] []))
    (fun args rets => Da.dvWit (V "da_verify" args rets) V)
    (fun args => piOf rd (V "verify_sub" args []) V)
    (fun args => aggHints rd (V "aggregate_claims" args []))

/-- **`main`, soundly, its witness decoded from the frame map** (G6's `MainSoundV`). -/
def main_sound_V (bytecode : List K) (piOf : Reader → Val → FrameMap → Proof) : Prop :=
  bytecode.length = 2 ^ bytecodeVars → ∀ (rd : Reader), MemOk rd → ∀ (C : CallRel) (V : FrameMap),
    UnfoldsV rd C V → CallRel.Le C (coreProgram.Rel rd) → ∀ (D : Digest) (σ : Val),
      LoadHolds rd 1 0 (digestScalars D).1 → LoadHolds rd 1 1 (digestScalars D).2 →
      Stmt.HoldsList C rd σ Data.core0.body False (fun rs ↦ rs = []) →
        statementDigest (decSeed σ) (decStmt σ rd) = D ∧
          NodeRel bytecode (decSeed σ) (decStmt σ rd) (decWitV σ rd V piOf)

theorem find_verify_sub : coreProgram.find? "verify_sub" = some Data.core18 :=
  Program.find?_of_indexOf? (j := 18) (by decide +kernel) rfl

/-- **`verify_sub`'s statement, its proof named by `piOf`**: on a memory image of at most `2^32`
words, under a call relation that unfolds at `V` and lies below `coreProgram.Rel`, a run of its
body whose arguments hold the exponent tables returns nothing, and its proof `piOf L.read σ V` is
accepted for the public input and the seed of its arguments. -/
def SubSoundW (bytecode : List K) (piOf : Reader → Val → FrameMap → Proof) : Prop :=
  bytecode.length = 2 ^ bytecodeVars → ∀ {κ : ℕ} (L : MemImage κ), κ ≤ 32 →
    ∀ (C : CallRel) (V : FrameMap), UnfoldsV L.read C V → CallRel.Le C (coreProgram.Rel L.read) →
      ∀ (σ : Val) (rets : List E),
        Stmt.HoldsList C L.read σ (Fn.body Data.core18) False (fun rs ↦ rs = rets) →
        VerifySub.VerifySubPre L.read (Data.core18.params.map σ) →
          rets = [] ∧ VerifySubOut bytecode L.read (Data.core18.params.map σ) (piOf L.read σ V)

/-- **`main` is sound, its witness decoded from the frame map**, given `verify_sub`'s statement
with its proof named. -/
theorem main_sound_V_of_sub {bytecode : List K} {piOf : Reader → Val → FrameMap → Proof}
    (hv : SubSoundW bytecode piOf) : main_sound_V bytecode piOf := by
  intro hbl rd hm C V hV hle D σ hp0 hp1 hb
  obtain ⟨κ, -, hκ, L, rfl⟩ := id hm
  refine main_sound_C hbl hm (unfolds_of_V hV) hle ⟨?_, ?_, ?_, ?_, ?_⟩ hp0 hp1 hb
  · intro p h
    obtain ⟨hp, hbx⟩ := body_ofV hV Sig.find_verify_lean_xmss h
    obtain ⟨-, ho⟩ := Sig.verify_lean_xmss_sound_holds C _ _ _ hbx
    have e : V "verify_lean_xmss" [p] [] (.n 0) = p := by
      rw [Sig.core19_params] at hp; simpa using hp
    rw [e] at ho
    exact ho
  · intro p h hbb
    obtain ⟨hp, hbs⟩ := body_ofV hV Sig.find_verify_sig_lean_sphincs h
    obtain ⟨-, ho⟩ := Sig.verify_sig_lean_sphincs_sound_holds C L hκ _ _ hbs
    rw [Sig.core20_params] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    obtain ⟨e0, e1⟩ := hp
    rw [e0, e1] at ho
    exact ho hbb
  · intro gsq rets h hsq
    obtain ⟨hp, hbd⟩ := body_ofV hV Da.find_da_verify h
    exact Da.da_verify_sound_w hV hle hm hp hbd hsq
  · intro pi0 pi1 s0 s1 glp gsq out h hexp
    obtain ⟨hp, hbv⟩ := body_ofV hV find_verify_sub h
    obtain ⟨-, ho⟩ := hv hbl L hκ C V hV hle _ _ hbv (by rw [hp]; exact hexp)
    rw [hp] at ho
    exact ho
  · intro ncg cpi cfresh ccarried dst h m hm1 hm16 hN
    obtain ⟨hp, hba⟩ := body_ofV hV find_aggregate_claims h
    exact (aggregate_claims_val hle hp hba m hm1 hm16 hN).2

end
end LeanVM.Guest.B1.Main
