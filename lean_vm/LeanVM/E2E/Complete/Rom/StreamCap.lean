/-
  LeanVM.E2E.Complete.Rom.StreamCap

  T6-prob, recursion: a proof the deferring verifier accepts has a stream of at most 1696 words,
  so the guest's stream cap (`End.Limits.stream`, 8192 words) holds of every honest child.
-/

module

public import LeanVM.E2E.Complete.Rom.NonVacuityN
public import LeanVM.Guest.B1.Comp.VsInv.Inv
public import LeanVM.Guest.B1.Main.HashH

/-!
# The stream cap holds of accepted proofs

`vs_inversionC`'s run decomposition (`Guest/B1/Comp/VsInv/Inv.lean`) without its tables' context
(the only part reading the cap): over any hash model, an accepted deferring verifier reads the
stream as the eight announced words, the stack's root, then GKR's, the tables', Flock's and the
stacked opening's words, each phase of the length its `Reads` lemma gives
(`Guest/B1/VerifySub/Consume.lean`). At a stack log at most 28 (the verifier's own check) these are
at most `10 + 1154 + 193 + 218 + 121 = 1696` words (`deferredStream_le`), within the cap
`Hints.streamCap = 8192`. So every child the H-oblivious prover outputs meets
`End.Limits.stream` (`honestOutN_stream_le`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.Value LeanVM.Protocol.LeanIsa LeanVM.Guest.B1.Main

@[expose] public section

/-- GKR reads at most `1154` words at a depth below `33`. -/
theorem gkrLen_le_cap : ∀ d < 33, gkrLen d ≤ 1154 := by decide

/-- The stacked opening reads at most `121` words at a stack log at most `28`. -/
theorem whirLen_le_cap : ∀ μ < 29, ∀ r < 5, whirLen μ r ≤ 121 := by decide

/-- Flock reads at most `218` words below `43` variables. -/
theorem flockLen_le_cap : ∀ n < 43, flockLen n ≤ 218 := by decide

theorem blake2sR1csLogSize_eq_14 : blake2sR1csLogSize = 14 := by decide

/-- The tables' phase reads at most `193` words when every row count has log below `29`. -/
theorem tablesLen_le_cap {bytecode : List K} {m : ℕ} {rows : List ℕ}
    (h : ∀ n ∈ rows, log2Ceil n < 29) : tablesLen (layoutOf bytecode m rows) ≤ 193 := by
  unfold tablesLen
  rw [layoutOf_heights]
  have hw : (tables.map Table.width).sum = 104 := by decide
  have hmax : ∀ (l : List ℕ) (a : ℕ), a ≤ 28 → (∀ x ∈ l, x ≤ 28) → l.foldl max a ≤ 28 := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x l ih =>
      intro a ha hx
      exact ih _ (max_le ha (hx x List.mem_cons_self)) fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)
  have := hmax (rows.map log2Ceil) 0 (by omega) fun x hx ↦ by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    have := h n hn
    omega
  rw [hw]
  omega

/-- **An accepted deferring verifier's stream has at most 1696 words**, over any hash model. -/
theorem deferredStream_le {M : HashModel} {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {seed pi : Digest} {c : FixedClaims} {π : Proof}
    (h : verifyDeferredWith M.H bytecode seed pi c π = some true) : π.stream.length ≤ 1696 := by
  obtain ⟨cv0, sF, -, hrun, hsF, -⟩ := verifyDeferredWith_inv (M := M) h
  unfold deferredProgram at hrun
  obtain ⟨u, sE, hE, hret⟩ := RunsM.bind_inv hrun
  obtain ⟨-, rfl⟩ := RunsM.pure_inv hret
  rw [verifyExecution_split] at hE
  obtain ⟨lr, s1, h1, hE⟩ := RunsM.bind_inv hE
  obtain ⟨u2, s2, h2, hE⟩ := RunsM.bind_inv hE
  obtain ⟨alphas, s3, h3, hE⟩ := RunsM.bind_inv hE
  obtain ⟨beta, s4, h4, hE⟩ := RunsM.bind_inv hE
  obtain ⟨gr, s5, h5, hE⟩ := RunsM.bind_inv hE
  obtain ⟨bc, s6, h6, hE⟩ := RunsM.bind_inv hE
  obtain ⟨fl, s7, h7, hE⟩ := RunsM.bind_inv hE
  obtain ⟨rs, s8, h8, h9⟩ := RunsM.bind_inv hE
  obtain ⟨logMem, rows, rate, rfl, e1s, -, -, -, -, -, -, hr2, hl, -, -, hs28⟩ :=
    vs_readSizes_invM hb h1
  obtain ⟨x0, x1, root, -, e2s, -, -, -⟩ := vs_commitStack_invM h2
  obtain ⟨-, hs3⟩ := RunsM.sampleN_inv h3
  obtain ⟨cB, -, rfl, rfl⟩ := RunsM.sampleE_inv h4
  obtain ⟨xsG, e5s, -, -, hG⟩ := RunsM.qfree (qfree_gkrPhase _) h5
  obtain ⟨xsT, e6s, -, -, hT⟩ := RunsM.qfree (qfree_tablesSeg _ _ _ _ _ _ _) h6
  obtain ⟨xsF, e7s, -, -, hF⟩ := RunsM.qfree (qfree_verifyFlock _ _) h7
  obtain ⟨mcs, -, hs8, -⟩ := vs_ringSwitch_invM h8
  unfold verifyStackedOpening at h9
  obtain ⟨lam, s9, h9a, h9⟩ := RunsM.bind_inv h9
  obtain ⟨cL, -, rfl, rfl⟩ := RunsM.sampleE_inv h9a
  rw [verifyWhir_split] at h9
  obtain ⟨w, s10, hw, hreq⟩ := RunsM.bind_inv h9
  obtain ⟨-, rfl⟩ := RunsM.require_inv hreq
  obtain ⟨xsW, osW, e10s, -, hW⟩ := RunsM.frame hw
  have e3s : s3.stream = s2.stream := by rw [hs3]
  have e8s : s8.stream = s7.stream := by rw [hs8]
  have hstream :
      π.stream = announce logMem rows rate ++ x0 :: x1 :: (xsG ++ (xsT ++ (xsF ++ xsW))) := by
    have e1s' : π.stream = announce logMem rows rate ++ s1.stream := e1s
    rw [e1s', e2s, ← e3s]
    change _ ++ _ :: _ :: s3.stream = _
    rw [e5s, e6s, e7s, ← e8s]
    rw [e10s, hsF]
    simp
  have hlb := layout_bounds hb hl hs28
  have hG' := (RunsToM.length_eq hG (reads_gkrPhase _)).1
  have hT' := (RunsToM.length_eq hT
    (reads_tablesSeg c (by simp [layoutOf_heights, hl, tables_length]) _ _ _ _ _)).1
  have hF' := (RunsToM.length_eq hF (reads_verifyFlock _ _)).1
  have hW' := (RunsWithM.length_eq hW (reads_whirOpen _ _ _)).1
  have hann : (announce logMem rows rate).length = 8 := by simp [announce, hl]
  have h1g := gkrLen_le_cap _ hlb.1
  have h1t := tablesLen_le_cap (bytecode := bytecode) (m := logMem) hlb.2
  have h1f : flockLen (blake2sR1csLogSize +
      (layoutOf bytecode logMem rows).tableLogHeights.getD opBlake2s 0) ≤ 218 := by
    refine flockLen_le_cap _ ?_
    rw [blake2sR1csLogSize_eq_14]
    have : (layoutOf bytecode logMem rows).tableLogHeights.getD opBlake2s 0 < 29 := by
      rw [layoutOf_heights, List.getD_eq_getElem?_getD]
      cases hx : (rows.map log2Ceil)[opBlake2s]? with
      | none => simp
      | some x =>
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hx)
        exact hlb.2 n hn
    omega
  have h1w := whirLen_le_cap (layoutOf bytecode logMem rows).stackLog (by omega) rate (by omega)
  dsimp only at hG' hT' hF' hW'
  rw [hstream]
  simp only [List.length_append, List.length_cons, hann, hG', hT', hF', hW']
  omega

/-- **Every child of the H-oblivious prover is within the stream cap.** -/
theorem honestOutN_stream_le (H : Bytes → Digest) {ρ pfuel : ℕ} (hρ : validRate ρ) {T : HonestTree}
    {o : HonestOutN} (h : honestOutN H ρ pfuel T = .ok o) :
    o.proof.stream.length ≤ Hints.streamCap := by
  obtain ⟨-, -, hacc, -⟩ := honestOutN_child H ρ pfuel hρ h
  have hv : verifyDeferredWith (hmOfC fun x ↦ some (H x)).H End.bytecode (seedOf H)
      (digestOf H o.stmt) o.fresh o.proof = some true := by
    show verifyDeferredWith (m := Option) (fun x ↦ some (H x)) _ _ _ _ _ = _
    rw [verifyDeferredWith_someH, hacc]
  have := deferredStream_le End.bytecode_length hv
  unfold Hints.streamCap
  omega

end
end LeanVM.E2E.Complete
