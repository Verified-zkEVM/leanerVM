/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedEqKids

  `verify_sub`'s hashing callees placed over a completeness model, their trees loading the
  transcript words they read: the interfaces and the callees' completeness.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedRoot

/-!
# `verify_sub`'s callees, their trees loading what they read

The image V_I decodes holds the frame cells and the trees' memory equations (`Tree.eqns`: the
loads, range checks and frame runs), not every buffer word. A word of the child proof's stream is
in the image when some instance loads it. `LoadsWords t c xs`: the tree `t` loads the words `xs`
at `g^c, g^(c+1), …` (each `(g^(c+k), xs[k])` among its equations).

* the hashing callees' placed shapes over the model with their trees loading the transcript words
  they read at the cursor `g^c` (`CompleteGkrAtWCL`, `CompleteTablesAtWCL`, `CompleteFlockAtWCL`,
  `CompleteOpenAtBCL`, the last with the opening's predicate `OsQ`, reader-free), each giving the
  earlier shape (`….toWC`, `CompleteOpenAtBCL.toBCT`);
* the calls before the dispatch complete with the transcript callees' loads (`vsKids1_completeWCL`,
  `VsKidsQ`), and the opening (`vsOpenKid_completeWCL`);
* `WordsAt rd s xs`: `rd` holds `xs` at `g^s, …`; from a tree's loads on any reader satisfying
  its equations (`wordsAt_of_loads`), and `streamAt` of it (`streamAt_of_wordsAt`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## Words loaded, words held -/

/-- **The tree loads the words `xs` at `g^c, g^(c+1), …`**: each is one of its memory equations. -/
def LoadsWords (t : Tree) (c : ℕ) (xs : List E) : Prop :=
  ∀ k (h : k < xs.length), (Parameters.gpow (c + k), xs[k]) ∈ t.eqns coreProgram

/-- **The reader holds `xs` at `g^s, g^(s+1), …`.** -/
def WordsAt (rd : Reader) (s : ℕ) (xs : List E) : Prop :=
  ∀ k (h : k < xs.length), rd (Parameters.gpow (s + k)) = some xs[k]

theorem wordsAt_of_loads {t : Tree} {c : ℕ} {xs : List E} (h : LoadsWords t c xs) {rd : Reader}
    (he : ∀ q ∈ t.eqns coreProgram, rd q.1 = some q.2) : WordsAt rd c xs :=
  fun k hk => he _ (h k hk)

theorem WordsAt.of_eq {rd : Reader} {s s' : ℕ} {xs : List E} (h : WordsAt rd s xs) (hs : s = s') :
    WordsAt rd s' xs := hs ▸ h

theorem WordsAt.append {rd : Reader} {s : ℕ} {xs ys : List E} (h1 : WordsAt rd s xs)
    (h2 : WordsAt rd (s + xs.length) ys) : WordsAt rd s (xs ++ ys) := by
  intro k hk
  by_cases h : k < xs.length
  · rw [List.getElem_append_left h]; exact h1 k h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (k - xs.length) (by simp at hk; omega)
    rwa [show s + xs.length + (k - xs.length) = s + k by omega] at this

theorem WordsAt.cons {rd : Reader} {s : ℕ} {x : E} {xs : List E} (h0 : rd (Parameters.gpow s) = some x)
    (h1 : WordsAt rd (s + 1) xs) : WordsAt rd s (x :: xs) := by
  intro k hk
  cases k with
  | zero => simpa using h0
  | succ k =>
    have := h1 k (by simp at hk; omega)
    rwa [show s + 1 + k = s + (k + 1) by omega] at this

/-- `streamAt` of words a reader holds. -/
theorem streamAt_of_wordsAt {rd : Reader} {s : ℕ} {xs : List E} (h : WordsAt rd s xs) :
    streamAt rd (ofK (Parameters.gpow s)) xs.length = xs := by
  refine List.ext_getElem (by simp [streamAt]) fun k h1 h2 => ?_
  simp only [streamAt, List.getElem_map, List.getElem_range, Main.addr_ofK, h k h2,
    Option.getD_some]

/-- The equations of a callee's tree are its caller's callees'. -/
theorem eqns_of_mem_kids {P : Core.Program} {k : Tree} :
    ∀ {ks : List Tree}, k ∈ ks → ∀ q ∈ k.eqns P, q ∈ Tree.eqnsKids P ks
  | [], h, _, _ => absurd h List.not_mem_nil
  | _ :: ks, h, q, hq => by
    rw [Tree.eqnsKids]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (eqns_of_mem_kids h q hq)

/-! ## Predicates: weaker, and bounds -/

section Mono

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}
  {κ : ℕ} {f : String} {Lin : Main.Layout} {args : List E} {Out : List E → Main.Layout → Prop}

theorem CompleteAtWST.mono {B : ℕ} {Bw : Θ → ℕ} {Q Q' : ℕ → Reader → Tree → Prop}
    (h : CompleteAtWST S fs cert w κ f Lin args Out B Bw Q) (hQ : ∀ fp rd t, Q fp rd t → Q' fp rd t) :
    CompleteAtWST S fs cert w κ f Lin args Out B Bw Q' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd', hw⟩ := hr rd hl hm
    ⟨t, hQ fp rd t hq, hn', hv, hb, hp, ht, hl', hd', hw⟩⟩

theorem CompleteAtWST.bmono {B B' : ℕ} {Bw : Θ → ℕ} {Q : ℕ → Reader → Tree → Prop}
    (h : CompleteAtWST S fs cert w κ f Lin args Out B Bw Q) (hB : B ≤ B') :
    CompleteAtWST S fs cert w κ f Lin args Out B' Bw Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn.trans hB, hr⟩

theorem CompleteAtBST.mono {B : ℕ} {Q Q' : ℕ → Reader → Tree → Prop}
    (h : CompleteAtBST S fs cert κ f Lin args Out B Q) (hQ : ∀ fp rd t, Q fp rd t → Q' fp rd t) :
    CompleteAtBST S fs cert κ f Lin args Out B Q' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hQ fp rd t hq, hn', hv, hb, hp, ht, hl', hd'⟩⟩

end Mono

/-! ## The hashing callees, their trees loading the words they read -/

section Placed

variable (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  {Θ : Type} (wt : Θ → String → ℕ)

/-- **`verify_bus_gkr` over the model, its tree loading the words it reads** (`CompleteGkrAtWC`):
the transcript words `xs` at `g^c`. -/
def CompleteGkrAtWCL (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest) (c z : ℕ)
    (Lin : Main.Layout), depth < 33 → RunsToM CM.hm (gkrPhase depth) cv xs r cv' →
    r.2.1.length = depth → r.2.2.length = 3 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) r.2.1) →
    CompleteAtWST CM.sem fs cert wt k "verify_bus_gkr" Lin [(digestScalars cv).1,
      (digestScalars cv).2, ofK (Parameters.gpow c), gen ^ depth, ofK (Parameters.gpow z)]
      (Returns ([(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length] ++ r.2.2)) B Bw fun _ _ t => LoadsWords t c xs

/-- **`verify_tables` over the model, its tree loading the words it reads**
(`CompleteTablesAtWC`). -/
def CompleteTablesAtWCL (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (pi : Digest) (logMem : ℕ) (alphas point values : List E) (cv : Digest) (xs : List E)
    (cv' : Digest) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim)
    (beta bv rm gzcn : E) (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (Lin : Main.Layout),
    bytecode.length = 2 ^ 22 →
    point.length = (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).depth →
    point.length < 33 → gzcn = gen ^ (layoutOf bytecode logMem rowsN).tableLogHeights.foldl max 0 →
    16 ≤ logMem → logMem ≤ 32 → alphas.length = 4 → values.length = 3 →
    rowsN.length = 6 → (∀ n ∈ rowsN, log2Ceil n < 29) → claims.length = nClaims →
    (∀ ev, BytecodeAtM CM.hm ev bytecode
        (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
      RunsToM CM.hm (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv xs
        (bus, claims) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun n ↦ gen ^ log2Ceil n)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) (claims.map (·.value)) ∧
      TCtx rd (layoutOf bytecode logMem rowsN) bus claims [ofK (Parameters.gpow z),
        ofK (Parameters.gpow chi), rm, gen ^ point.length, gzcn, ofK (Parameters.gpow cplen)]) →
    CompleteAtWST CM.sem fs cert wt k "verify_tables" Lin
      [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), (digestScalars pi).1,
        (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), values.getD 0 0, values.getD 1 0,
        values.getD 2 0]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, gzcn, bv, rm]) B Bw fun _ _ t => LoadsWords t c xs

/-- **`verify_flock` over the model, its tree loading the words it reads**
(`CompleteFlockAtWC`). -/
def CompleteFlockAtWCL (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (τ : ℕ) (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E)
    (c zc lr zp : ℕ) (Lin : Main.Layout), τ < 29 → chi.length = 8 + τ → rcs.length = 8 →
    s.length = 64 →
    (∀ ev, MatricesAtM CM.hm ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsToM CM.hm (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow zc)) chi ∧
      ReadsAt rd (ofK (Parameters.gpow lr)) rcs ∧ ReadsAt rd (ofK (Parameters.gpow zp)) s) →
    CompleteAtWST CM.sem fs cert wt k "verify_flock" Lin [(digestScalars cv).1,
      (digestScalars cv).2, ofK (Parameters.gpow c), gen ^ τ, ofK (Parameters.gpow zc),
      ofK (Parameters.gpow lr), ofK (Parameters.gpow zp)]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, zSkip, alpha, mv]) B Bw
      fun _ _ t => LoadsWords t c xs

/-- **`open_stacked` over the model, its tree loading the words it reads and satisfying the
opening's predicate** (`CompleteOpenAtBCT`): `OsQ μ r os fp t`, reader-free, the Whir side's
statement that the tree `t` at `fp` decodes to the openings `os`. -/
def CompleteOpenAtBCL (CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop)
    (B : ℕ) (OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root cv : Digest) (xs : List E) (os : List Opening) (w : WhirEnd) (cv' : Digest)
      (roots' : List (Digest × ℕ × ℕ)) (target : E) (c : ℕ) (Lin : Main.Layout),
      RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' →
      CapOk μ r root cv xs os target →
      (∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) →
      CompleteAtBST CM.sem fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2,
        target, (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)]
        (fun rets Lout =>
          ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
            Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) B
        fun fp _ t => LoadsWords t c xs ∧ OsQ μ r os fp t

end Placed

section Forget

variable {CM : CompModel} {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {bytecode : List K}
  {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
  {Θ : Type} {wt : Θ → String → ℕ} {B : ℕ} {Bw : Θ → ℕ}

theorem CompleteGkrAtWCL.toWC (h : CompleteGkrAtWCL CM fs cert k wt B Bw) :
    CompleteGkrAtWC CM fs cert k wt B Bw := by
  intro cv depth xs r cv' c z Lin h1 h2 h3 h4 hm
  exact (h cv depth xs r cv' c z Lin h1 h2 h3 h4 hm).toWS

theorem CompleteTablesAtWCL.toWC (h : CompleteTablesAtWCL CM fs cert k bytecode TCtx wt B Bw) :
    CompleteTablesAtWC CM fs cert k bytecode TCtx wt B Bw := by
  intro pi logMem alphas point values cv xs cv' rowsN bus claims beta bv rm gzcn c z lp sq dims rows
    bk fpw pool cplen chi Lin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hrun hm
  exact (h pi logMem alphas point values cv xs cv' rowsN bus claims beta bv rm gzcn c z lp sq dims
    rows bk fpw pool cplen chi Lin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hrun hm).toWS

theorem CompleteFlockAtWCL.toWC (h : CompleteFlockAtWCL CM fs cert k wt B Bw) :
    CompleteFlockAtWC CM fs cert k wt B Bw := by
  intro τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4 hrun hm
  exact (h τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4 hrun hm).toWS

theorem CompleteOpenAtBCL.toBCT {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop} (h : CompleteOpenAtBCL CM fs cert k CapOk B OsQ) :
    CompleteOpenAtBCT CM fs cert k CapOk B fun μ r os fp _ t => OsQ μ r os fp t := by
  intro μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm
  exact CompleteAtBST.mono (h μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm)
    fun _ _ _ h => h.2

end Forget

/-! ## The callees' completeness -/

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData} {R : VsRunC}
  {CM : CompModel} {fp lpA sqA outA : ℕ} {Θ : Type}

/-- **The transcript callees' predicates before the dispatch**: `verify_bus_gkr`, `verify_tables`
and `verify_flock` load the stream's GKR, tables and Flock words where `verify_sub`'s stream
buffer (at `g^(vsB fs fp D 2)`) holds them. -/
def VsKidsQ (fs : String → ℕ) (fp : ℕ) (D : VsData) (k : Kid) (_b : ℕ) (_rd : Reader) (t : Tree) :
    Prop :=
  (k.f = "verify_bus_gkr" → LoadsWords t (vsB fs fp D 2 + 10) D.xsG) ∧
  (k.f = "verify_tables" → LoadsWords t (vsB fs fp D 2 + 10 + D.xsG.length) D.xsT) ∧
  (k.f = "verify_flock" → LoadsWords t (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) D.xsF)

/-- **The calls before the dispatch are complete within weights over the model, the transcript
callees loading their words** (`vsKids1_completeWC`). -/
theorem vsKids1_completeWCL {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R)
    (htok : D.TOk bytecode) {Bs : VsBounds} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w)
    {Bsw : VsBoundsW Θ} (hG : CompleteGkrAtWCL CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWCL CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWCL CM fs cert κ w Bs.fl Bsw.fl) (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hκ : 7 ≤ κ) :
    ∀ k ∈ vsKids1C fs D R fp lpA sqA outA, k.taken = true →
      CompleteAtWST CM.sem fs cert w κ k.f k.Lin k.args k.Out (vsBd fs Bs k)
        (vsBdWS w H Bsw k) (VsKidsQ fs fp D k) := by
  intro k hk ht
  have hold := vsKids1_completeWC hb hok htok H hG.toWC hT.toWC hF.toWC hPl hκ k hk ht
  have M := fun rd (hm : MemL rd (vsAllLC fs D R fp lpA sqA outA)) =>
    vsAll_memC (off := 0) (kap := 0) (pt := 0) hm
  have CE := cur_eqs (fs := fs) (fp := fp) (D := D) (off := 0) (kap := 0) (pt := 0)
  have hfree : ∀ (k : Kid), k.f ≠ "verify_bus_gkr" → k.f ≠ "verify_tables" →
      k.f ≠ "verify_flock" → ∀ b rd t, VsKidsQ fs fp D k b rd t :=
    fun k h1 h2 h3 _ _ _ => ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h3⟩
  simp only [vsKids1C, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact CompleteAtWST.mono (CompleteAtWS.toWST hold) fun _ _ _ _ =>
        hfree _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide) _ _ _
    | skip
  · have h := hG R.cvB _ D.xsG D.gr D.cvG (vsB fs fp D 2 + 10) (vsB fs fp D 7) _ hok.depth_lt hok.gkr
      hok.point_length hok.values_length fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).1
        rwa [CE.1] at this, (M rd hm).1.zeta⟩
    rw [← hok.point_length, depth_eqC hb hok, values_eqC hok, ← CE.1] at h
    exact CompleteAtWST.mono ((CompleteAtWST.bmono h (by vs_bd)).wmono fun θ => by vs_bdwS)
      fun _ _ _ hL => ⟨fun _ => hL, fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide)⟩
  · have h := hT D.pi D.logMem R.alphas D.gr.2.1 D.gr.2.2 D.cvG D.xsT D.cvT D.rows D.bus D.claims
      R.beta D.bv D.rm D.gzcn (vsB fs fp D 2 + 10 + D.xsG.length) (vsB fs fp D 7) lpA sqA
      (vsB fs fp D 4) (vsB fs fp D 3) (vsB fs fp D 6) (vsB fs fp D 9) (vsB fs fp D 0)
      (vsB fs fp D 1) (vsB fs fp D 10) _ hb (by
        rw [hok.point_length]; unfold pushDepth; rw [layoutOf_logBytecode hb]; rfl)
      (by rw [hok.point_length]; exact hok.depth_lt) (by rw [htok.gzcn, htok.chis_len])
      hok.logMem_ge hok.logMem_le R.alphas_length hok.values_length
      hok.rows_length hok.rows_log hok.claims_length hok.tables fun rd _ hm => by
        obtain ⟨h0, ht, hc, hp⟩ := M rd hm
        refine ⟨?_, h0.zeta, ht, h0.rows, ?_, ?_, h0.fpw, h0.pool, tctx_ofC hok htok h0.zeta hc hp⟩
        · have := (stream_at hok.rows_length h0.stream).2.1
          rwa [CE.2.1] at this
        · have := h0.dims
          rwa [dims_eq] at this
        · have := h0.bk
          rwa [hsMap_eq] at this
    rw [← CE.2.1, depth_eqC hb hok] at h
    exact CompleteAtWST.mono ((CompleteAtWST.bmono h (by vs_bd)).wmono fun θ => by vs_bdwS)
      fun _ _ _ hL => ⟨fun h => absurd h (by dsimp only; decide), fun _ => hL, fun h => absurd h (by dsimp only; decide)⟩
  · have h := hF D.tau D.cvT D.xsF D.cvF D.zSkip D.alpha D.mv D.chi D.rcs D.s
      (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) (vsB fs fp D 11) (vsB fs fp D 12)
      (vsB fs fp D 13) _ (tau_ltC hok) hok.chi_length hok.rcs_length hok.s_length hok.flock
      fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).2.2.1
        rwa [CE.2.2.1] at this, (M rd hm).1.zchis, (M rd hm).1.lrs, (M rd hm).1.zpart⟩
    rw [← CE.2.2.1] at h
    exact CompleteAtWST.mono ((CompleteAtWST.bmono h (by vs_bd)).wmono fun θ => by vs_bdwS)
      fun _ _ _ hL => ⟨fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide), fun _ => hL⟩

/-- The stream's opening words' cursor: `verify_sub`'s stream buffer past the sizes, the root,
GKR's, the tables' and Flock's words. -/
def vsCurW (fs : String → ℕ) (fp : ℕ) (D : VsData) : ℕ :=
  vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length + D.xsF.length

/-- **The opening is complete within weights over the model, its tree loading the opening's
words, satisfying `OsQ`, placed** (`vsOpenKid_completeWCT`). -/
theorem vsOpenKid_completeWCL {κ : ℕ}
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop} {B : ℕ}
    {OsQ : ℕ → ℕ → List Opening → ℕ → Tree → Prop}
    {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) (hok : D.OkC CM bytecode R)
    (hO : CompleteOpenAtBCL CM fs cert κ CapOk B OsQ)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D)) :
    let k := vsOpenKidC fs bytecode D R fp lpA sqA outA
    CompleteAtWST CM.sem fs cert w κ k.f k.Lin k.args k.Out B (fun θ => H.os θ)
      fun b _ t => (LoadsWords t (vsCurW fs fp D) D.xsW ∧
        OsQ (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.os b t) ∧
        t.Placed coreProgram fs cert b := by
  intro k
  have h := hO _ D.rate hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le D.root R.cvL D.xsW D.os D.w
    D.cvW D.roots' (R.target D) (vsCurW fs fp D) (vsAllLC fs D R fp lpA sqA outA) hok.opening hcap
    fun rd _ hm => by
      have := (stream_at hok.rows_length
        (vsAll_memC (off := 0) (kap := 0) (pt := 0) hm).1.stream).2.2.2
      rwa [curW_eq] at this
  have hc : curW D (vsPtrsAt fs fp D 0 0 0) = ofK (Parameters.gpow (vsCurW fs fp D)) := curW_eq
  rw [← hc] at h
  exact CompleteAtBST.toWST_weightLe (CompleteAtBST.placed h) fun θ =>
    H.os_le θ _ _ hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le

end
end LeanVM.Guest.B1.VerifySub
