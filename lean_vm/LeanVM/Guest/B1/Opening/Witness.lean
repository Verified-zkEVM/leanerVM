/-
  LeanVM.Guest.B1.Opening.Witness

  `opening_queries`' witness read off its frames: each query's position, row and siblings below
  the cap, as functions of the valuations (the witness convention, `B1/Main/Frames.lean`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesRow
public import LeanVM.Guest.B1.Main.Frames

/-!
# `opening_queries`' witness, named

The witness convention (G6, 2026-10-23): a witness is a function of the function's own valuation
and the frame map `V`, reading words only (no hash, no verifier function, no choice).

**A query's witness** (`QW`): its position, its row and its siblings below the cap.

* `posOf rd bp D`: the position whose `D` bits the run at `bp` holds (`memRead`, the memory's
  word, `0` where it has none);
* `oqSibsOf pd ch q σ`: the siblings below the cap, read off the children cells `ch ..` of the
  frame: at level `l` the pair on the side the position's bit does not select (`pathCell`);
* `oqQueryW s rd bp b emit σ`: the query hinted at `b`, its bit pointer `bp` (`oqRow` its row);
* `oqIterOf s rd σ`: a loop iteration's queries (two at level 0, one deeper), from its frame;
* `oqsOf s odd loop N rd σ V`: the function's queries, from its frame `σ` (the odd first query at
  level 0) and the frames `V loop (g^j :: ps) []` of its `N` iterations, `ps` the loop's other
  arguments (`oqLoopArgs σ`).

**What the witness satisfies.** `QueryOpensS` is `QueryOpens` with the siblings named;
`MeaningOpeningQueriesW … ws` is `MeaningOpeningQueries` with the queries' positions, rows and
siblings those of `ws`. `opening_queries_sound_w_Spec`: under a call relation `C ≤ Rel` that
unfolds at `V` (`UnfoldsV`), a valuation `σ` holding the body of a deployed specialization, its
bit pointers pointing to bits, gives `MeaningOpeningQueriesW` at `oqsOf … σ V`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Reading words -/

/-- The memory's word at `p·g^off` (`0` where it has none). -/
def memRead (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * Parameters.gpow off)).getD 0

/-- The `n` words of the run at `p`. -/
def readN (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (memRead rd p)

/-- The digest of two cells (the zero digest when they are not one's). -/
def digestOfCells (a b : E) : Digest := (digestOfScalars (a, b)).getD (Vector.replicate 4 0)

/-- The position whose `D` bits the run at `bp` holds as `0`/`1` words. -/
def posOf (rd : Reader) (bp : E) (D : ℕ) : ℕ := bitsVal (fun l ↦ decide (memRead rd bp l = 1)) D

/-! ## A query's witness -/

/-- A query's witness: its position, its row and its siblings below the cap. -/
abbrev QW : Type := ℕ × List K × List Digest

/-- The siblings below the cap of the query at `q`, read off the children cells `ch ..`: at
level `l` the pair on the side the bit does not select. -/
def oqSibsOf (pd ch q : ℕ) (σ : Val) : List Digest :=
  (List.range pd).map fun l ↦
    digestOfCells (σ (.n (ch + 4 * l + (if q.testBit l then 0 else 2))))
      (σ (.n (ch + 4 * l + (if q.testBit l then 0 else 2) + 1)))

/-- The query hinted at `b` (bit pointer `bp`), from its frame `σ`. -/
def oqQueryW (s : Oq) (rd : Reader) (bp : E) (b : ℕ) (emit : Bool) (σ : Val) : QW :=
  (posOf rd bp (s.pd + s.cd), oqRow b s.R σ,
    oqSibsOf s.pd (oqCh s b emit) (posOf rd bp (s.pd + s.cd)) σ)

/-- A loop iteration's queries, from its frame: two at level 0 (`base = 1`), one deeper. -/
def oqIterOf (s : Oq) (rd : Reader) (σ : Val) : List QW :=
  if s.base = 1 then
    [oqQueryW s rd (σ (.n 10)) 11 true σ, oqQueryW s rd (σ (.n (oqE1 s))) (oqE1 s + 1) false σ]
  else [oqQueryW s rd (σ (.n 9)) 10 true σ]

/-- The loop's arguments after its counter (`oqMainT`'s call). -/
def oqLoopArgs (σ : Val) : List E :=
  [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1), σ (.n 5), σ (.n 11), σ (.n 8)]

/-- **The queries of `opening_queries`**, from its frame `σ` and its `N` iterations' frames. -/
def oqsOf (s : Oq) (odd : ℕ) (loop : String) (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    List QW :=
  (if odd = 1 then [oqQueryW s rd (σ (.n 12)) 13 true σ] else []) ++
    (List.range N).flatMap fun j ↦ oqIterOf s rd (V loop (gen ^ j :: oqLoopArgs σ) [])

/-! ## What the witness satisfies -/

/-- **`QueryOpens` with the siblings below the cap named.** -/
def QueryOpensS (rd : Reader) (base I depth cd : ℕ) (cap flags wp : E) (q : ℕ) (row : List K)
    (sibs : List Digest) (d : E) : Prop :=
  row.length = (if base = 1 then I else 3 * I) ∧ sibs.length = depth - cd ∧
    ∃ (w : ℕ → E) (pp : E),
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) ∧
      IsInK pp ∧
      (∀ k < 4 * (depth - cd), ∀ x, rd (pp.limb 0 * Parameters.gpow k) = some x →
        x = pathCell (hashWords row) q sibs k) ∧
      (∀ l < depth - cd,
        LoadHolds rd (pp * gen ^ (if q.testBit l then 2 else 0)) (4 * l)
          (digestScalars (climbNode (hashWords row) q sibs l)).1 ∧
        LoadHolds rd (pp * gen ^ (if q.testBit l then 2 else 0)) (4 * l + 1)
          (digestScalars (climbNode (hashWords row) q sibs l)).2) ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)))
        (digestScalars (climbD (hashWords row) q sibs)).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)) + 1)
        (digestScalars (climbD (hashWords row) q sibs)).2 ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1 ∧
      d = rowDot base I row w

/-- **`opening_queries`' meaning, its queries those of `ws`**: as `MeaningOpeningQueries`, query
`k` at the position `ws[k].1`, opening the row `ws[k].2.1` with the siblings `ws[k].2.2`. -/
def MeaningOpeningQueriesW (odd base I depth cd : ℕ) (rd : Reader) (ws : List QW) :
    List E → List E → Prop
  | [cap, flags, lam, lamN, qptrs, wp, nG], rets =>
      ∃ N < ordG, nG = gen ^ N ∧ lam ≠ 0 ∧ ws.length = oqCount odd base N ∧
        ∃ (bps : ℕ → E) (ds : ℕ → E),
          (∀ k < oqCount odd base N, LoadHolds rd qptrs k (bps k) ∧
            (ws.getD k default).1 < 2 ^ depth ∧
            (∀ l < depth, LoadHolds rd (bps k) l (bitE ((ws.getD k default).1.testBit l))) ∧
            QueryOpensS rd base I depth cd cap flags wp (ws.getD k default).1
              (ws.getD k default).2.1 (ws.getD k default).2.2 (ds k)) ∧
          ∃ ch : E, (∀ i ≤ N, LoadHolds rd ch i (oqChain odd base lam⁻¹ ds i)) ∧
            rets = [oqChain odd base lam⁻¹ ds N * lamN]
  | _, _ => False

/-- The deployed specializations with their loop helpers and shapes: `(name, loop, shape, odd)`. -/
def openingQueriesLoops : List (String × String × Oq × ℕ) :=
  [("opening_queries__L0_L1_L64_L32_L17_L8", "__loop361", ⟨1, 64, 9, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L19_L8", "__loop368", ⟨1, 64, 11, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L21_L6", "__loop408", ⟨1, 64, 15, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L22_L7", "__loop390", ⟨1, 64, 15, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L24_L7", "__loop393", ⟨1, 64, 17, 7⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L20_L7", "__loop398", ⟨1, 64, 13, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L23_L7", "__loop401", ⟨1, 64, 16, 7⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L14_L5", "__loop364", ⟨0, 16, 9, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L16_L6", "__loop362", ⟨0, 16, 10, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L18_L4", "__loop383", ⟨0, 16, 14, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L19_L5", "__loop376", ⟨0, 16, 14, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L20_L6", "__loop375", ⟨0, 16, 14, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L22_L4", "__loop416", ⟨0, 16, 18, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L23_L6", "__loop394", ⟨0, 16, 17, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L18_L7", "__loop384", ⟨1, 64, 11, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L20_L6", "__loop407", ⟨1, 64, 14, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L21_L7", "__loop388", ⟨1, 64, 14, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L23_L6", "__loop410", ⟨1, 64, 17, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L25_L6", "__loop412", ⟨1, 64, 19, 6⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L21_L7", "__loop399", ⟨1, 64, 14, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L23_L8", "__loop380", ⟨1, 64, 15, 8⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L15_L5", "__loop363", ⟨0, 16, 10, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L17_L4", "__loop389", ⟨0, 16, 13, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L18_L5", "__loop373", ⟨0, 16, 13, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L19_L6", "__loop372", ⟨0, 16, 13, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L21_L4", "__loop406", ⟨0, 16, 17, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L22_L5", "__loop395", ⟨0, 16, 17, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L24_L5", "__loop413", ⟨0, 16, 19, 5⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L18_L8", "__loop365", ⟨1, 64, 10, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L20_L7", "__loop386", ⟨1, 64, 13, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L21_L8", "__loop374", ⟨1, 64, 13, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L23_L7", "__loop391", ⟨1, 64, 16, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L26_L6", "__loop414", ⟨1, 64, 20, 6⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L22_L7", "__loop400", ⟨1, 64, 15, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L24_L7", "__loop402", ⟨1, 64, 17, 7⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L16_L4", "__loop387", ⟨0, 16, 12, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L17_L5", "__loop370", ⟨0, 16, 12, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L18_L6", "__loop369", ⟨0, 16, 12, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L20_L4", "__loop396", ⟨0, 16, 16, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L21_L5", "__loop382", ⟨0, 16, 16, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L22_L6", "__loop381", ⟨0, 16, 16, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L24_L6", "__loop404", ⟨0, 16, 18, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L19_L7", "__loop385", ⟨1, 64, 12, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L20_L8", "__loop371", ⟨1, 64, 12, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L22_L6", "__loop409", ⟨1, 64, 16, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L24_L6", "__loop411", ⟨1, 64, 18, 6⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L19_L7", "__loop397", ⟨1, 64, 12, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L22_L8", "__loop377", ⟨1, 64, 14, 8⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L25_L7", "__loop403", ⟨1, 64, 18, 7⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L16_L5", "__loop367", ⟨0, 16, 11, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L17_L6", "__loop366", ⟨0, 16, 11, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L19_L4", "__loop392", ⟨0, 16, 15, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L20_L5", "__loop379", ⟨0, 16, 15, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L21_L6", "__loop378", ⟨0, 16, 15, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L23_L5", "__loop405", ⟨0, 16, 18, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L25_L5", "__loop415", ⟨0, 16, 20, 5⟩, 0)]

/-- The loop helper of a specialization. -/
def oqLoopOf (name : String) : String :=
  ((openingQueriesLoops.find? (·.1 = name)).map (·.2.1)).getD ""

/-- **`opening_queries` is sound with its queries named** at the specialization `name` (loop
helper `loop`, shape `s`, `odd`): under a call relation `C ≤ Rel` unfolding at `V`, a valuation
`σ` holding its body on `args` returning `rets`, `N` iterations (`args[6] = g^N`) and the bit
pointers pointing to bits, its meaning holds with the queries `oqsOf s odd loop N rd σ V`. -/
def opening_queries_sound_w_Spec (name loop : String) (s : Oq) (odd : ℕ) : Prop :=
  ∀ (rd : Reader) (C : CallRel) (V : FrameMap), UnfoldsV rd C V →
    CallRel.Le C (coreProgram.Rel rd) →
    ∀ (fm : Fn) (σ : Val) (args rets : List E) (N : ℕ), coreProgram.find? name = some fm →
      fm.params.map σ = args → Stmt.HoldsList C rd σ fm.body False (fun rs ↦ rs = rets) →
      args.getD 6 0 = gen ^ N → N < ordG →
      QueryBitsBool rd (args.getD 4 0) (oqCount odd s.base N) (s.pd + s.cd) →
      MeaningOpeningQueriesW odd s.base s.I (s.pd + s.cd) s.cd rd (oqsOf s odd loop N rd σ V)
        args rets

/-- Every deployed specialization of `opening_queries` is sound with its queries named. -/
def opening_queries_all_sound_w_Spec : Prop :=
  ∀ p ∈ openingQueriesLoops, opening_queries_sound_w_Spec p.1 p.2.1 p.2.2.1 p.2.2.2

end
end LeanVM.Guest.B1
