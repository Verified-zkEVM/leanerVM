/-
  LeanVM.Guest.B1.VerifySub.KnownB

  The control-flow obligation at `verify_sub`'s terminal call over a hash model: once the body
  has run up to it under the model's semantics, every committed column's log in `col_kappas` is
  below `29`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.VerifySub.ChallengesB
public import LeanVM.Guest.B1.VerifySub.InterfaceM
public import LeanVM.Guest.SoundB

/-!
# `col_kappas` is in range at `check_opening_terminal`, over a hash model

`Known.lean` over a hash model `M`: `vs_knownB` is `vs_known` with `verify_sub`'s first `1927`
statements holding under `M.sem`, from `verify_bus_gkr`'s and `verify_tables`' soundness over the
model (`SoundGkrM`, `SoundTablesM`), and `vsKnownB_model` is `End.VsKnownB M.sem`, the hypothesis
`End.mainBodyLB_of` takes.

The proof is `vs_known`'s. Of what it reads, only the public input's cells hash (they are the
message of the seed's compression, canonical by `M.canonical`, `vs_seedM`), and only the GKR and
the tables' calls are hashing callees (their outcomes over the model give the same point, values,
row counts and heights); every other fact is read off runs free of `BLAKE2S`, as deployed
(`VsHoldsToB.sliceF'`), and `certify_placement` and the logs are free of `BLAKE2S`
(`relB_vsFree`), so their deployed lemmas apply.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`col_kappas` is in range at the terminal call, over a hash model** (`vs_known`). -/
theorem vs_knownB {M : HashModel} {bytecode : List K}
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop} {κ : ℕ} (hκ : κ ≤ 32)
    (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (hgkr : SoundGkrM M Lm.read)
    (htab : SoundTablesM M bytecode TCtx Lm.read) (σ : Val)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5)))
    (h : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem Lm.read) Lm.read σ
      ((Fn.body Data.core15).take 1927) True (fun _ ↦ True)) :
    ∀ c < 92, ∃ e < 29, LoadHolds Lm.read (σ (.n 1631)) c (ofK (gpow e)) := by
  have hv : VsHoldsToB M.sem 1927 Lm.read σ := by rw [body_take_1927] at h; exact h
  -- the public input, the memory's log, the kappas
  obtain ⟨-, pi, -, -, hpi, -, -⟩ := vs_seedM hv (by decide)
  obtain ⟨m, hm1, hm2, -, h144⟩ := vs_logMemB hκ hκ6 Lm hv (by decide) ht
  obtain ⟨hdims, hbase, hbk⟩ := vs_kappasB hv (by decide)
  -- the bus challenges, as stored
  have hst : ∀ k < 4, LoadHolds Lm.read (σ (.n 451)) k (σ (.n (452 + 14 * k + 13))) := by
    have hs : ∀ k < 4, (decide (551 + 15 * k + 1 ≤ 1927) && stmtsEqb
        [.atom (.load (.n (452 + 14 * k + 13)) (.n 451) k)] ((vsPre.drop (551 + 15 * k)).take 1) &&
        Stmt.freeInList vsFree [.atom (.load (.n (452 + 14 * k + 13)) (.n 451) k)]) = true := by
      decide +kernel
    exact fun k hk => hv.atomF' _ _ (hs k hk)
  set alphas := [σ (.n 465), σ (.n 479), σ (.n 493), σ (.n 507)]
  have har : ReadsAt Lm.read (σ (.n 451)) alphas := fun k hk => by
    simp only [alphas, List.length_cons, List.length_nil] at hk
    match k, hk with
    | 0, _ => exact hst 0 (by omega)
    | 1, _ => exact hst 1 (by omega)
    | 2, _ => exact hst 2 (by omega)
    | 3, _ => exact hst 3 (by omega)
  have hfpw := vs_fpwB hv (by decide) (alphas := alphas) rfl har
  -- GKR
  have cG := hv.call' 806 "verify_bus_gkr" [.n 690, .n 691, .n 700, .n 417, .n 418]
    [.n 701, .n 702, .n 703, .n 704, .n 705, .n 706] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cG
  obtain ⟨-, depth, xsG, gr, cvG, -, h417, hdepth, -, -, hptl, -, hzeta, hretsG⟩ :=
    hgkr _ _ _ _ _ _ cG
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hretsG
  obtain ⟨-, -, -, hgr⟩ := hretsG
  -- the tables
  have cT := hv.call' 810 "verify_tables" [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417,
    .n 143, .n 30, .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706]
    [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cT
  rw [h144] at hdims hbk hbase
  have hpre : TablesPre Lm.read (σ (.n 4)) pi m alphas gr.2.1 gr.2.2
      [σ (.n 707), σ (.n 708), σ (.n 703), σ (.n 0), σ (.n 1), σ (.n 418), σ (.n 417),
        σ (.n 143), σ (.n 30), σ (.n 163), σ (.n 5), σ (.n 508), σ (.n 698), σ (.n 7), σ (.n 8),
        σ (.n 709), σ (.n 704), σ (.n 705), σ (.n 706)] :=
    ⟨hpi, hzeta, by rw [h417, hptl], by omega, hm1, hm2,
      ⟨dimsWords σ, by simp [dimsWords], hdims, hbk⟩, ht, rfl, hfpw, hgr.symm⟩
  obtain ⟨-, -, -, rowsN, -, -, -, hrl, -, hdimsR, hlogs, -⟩ := htab _ _ _ _ _ _ _ _ hpre cT
  have hdw : dimsWords σ = (rowsN.map log2Ceil).map (gen ^ ·) := by
    have := readsAt_unique (by simp [dimsWords, hrl]) hdims hdimsR
    rw [List.cons.injEq] at this
    rw [this.2, List.map_map]
    rfl
  have hhs : ∀ h ∈ rowsN.map log2Ceil, h < 29 := by
    intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hlogs n hn
  have hhl : (rowsN.map log2Ceil).length = 6 := by simp [hrl]
  -- the placement
  have cP := hv.callF' 1913 "certify_placement" [.n 155, .n 5] [.n 1629, .n 1630, .n 1631]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cP
  rw [hdw] at hbase
  obtain ⟨off, kap, hretsP, hpctx⟩ := soundPlace hκ Lm _ _ _ m _ _ ht hm2 hhl hhs hbase cP
  simp only [List.cons.injEq] at hretsP
  obtain ⟨r1629, -, r1631, -⟩ := hretsP
  -- the stack's log, from the range check before the dispatch
  have cL := hv.callF' 1914 "log2_ceil_in_the_exponent__L15_L34" [.n 1629, .n 4, .n 5] [.n 1632]
    (by decide +kernel)
  obtain ⟨N, hN, hg, hl34, -, -, hr⟩ := (log2_ceil_in_the_exponent_L15_L34_iff hκ hκ6 Lm ht _).mp cL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
  have hs := hv.sliceF' 1915 [.atom (.const (.n 1633) (word 8198552432976855044 0 0)),
    .atom (.mul (.n 1634) (.n 1632) (.n 1633)), .atom (.const (.n 1635) (word 64 0 0)),
    .atom (.rangeCheck (.n 1634) (.n 1636) (.n 1637) (.n 1638) (.n 1635))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨e1633, e1634, e1635, ⟨q1, q2, q3⟩⟩ := hs
  obtain ⟨e, he, hxe⟩ := rc_gen hκ hκ6 Lm (K := 7) (by decide) (by decide)
    (by rw [e1635]; exact word_two_pow (a := 6) (by decide)) q1 q2 q3
  have hμ : gen ^ max 15 (log2Ceil N) = gen ^ (e + 22) := by
    rw [← hr, pow_add, ← hxe, e1634, e1633, mul_assoc, minShiftInv, mul_one]
  have hμe := gen_pow_inj (by omega) (by omega) hμ
  have hST := stackTotal_lt m (rowsN.map log2Ceil) hm2 hhs
  rw [r1629] at hg
  have eST := gen_pow_inj (by omega) (by omega) hg
  -- the columns' logs
  have hkb := hypKappa Lm.read _ _ _ hpctx (by rw [eST]; omega)
  intro c hc
  obtain ⟨k, hk, hl⟩ := hkb c hc
  exact ⟨k, hk, by rw [r1631, ← gen_pow_eq_ofK]; exact hl⟩

/-- **`End.VsKnownB` over a hash model**, from `verify_bus_gkr`'s and `verify_tables`' soundness
over the model on every memory `MemOk` admits: the hypothesis of `End.mainBodyLB_of` at
`M.sem`. -/
theorem vsKnownB_model {M : HashModel} {bytecode : List K}
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    (hgkr : ∀ rd, Main.MemOk rd → SoundGkrM M rd)
    (htab : ∀ rd, Main.MemOk rd → SoundTablesM M bytecode TCtx rd) : End.VsKnownB M.sem := by
  intro rd hm σ ht h
  obtain ⟨κ, h16, h32, L, rfl⟩ := hm
  exact vs_knownB h32 (by omega) L (hgkr _ ⟨κ, h16, h32, L, rfl⟩) (htab _ ⟨κ, h16, h32, L, rfl⟩)
    σ ht h

end
end LeanVM.Guest.B1.VerifySub
