module

public import LeanVM.Guest.Fast.WhirTablesCheck
public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# `verify_sub`'s child proof reader, computable

`vsPiOf rd σ V` (`B1/VerifySub/Proof.lean`) reads the child proof off `verify_sub`'s valuation,
the memory and the frame map `V : String → …`, through `open_stacked`'s template at the
configuration `osCfg m` (`osQCalls`, `osWordsLen`, the `LIG_*` tables) and a classical exponent
search (`dispatchIdx`). `vsPiOfN rd σ Vn cl` reads the same words off the literal tables of
`Fast/WhirTables.lean`, the frames numbered (`Vn k = V (decoderFunctionName k)`,
`Fast/FunctionNames.lean`) and the cursor's length a parameter `cl` (`cursorLen`);
`vsPiOfN_eq`: they are equal; `openNames_eq`: `open_stacked`'s specializations are the functions
`openStackedIdx m`.

* `oqsOfN`: `opening_queries`' queries (`oqsOf`), its loop's frames numbered;
* `levelOsN`: a level's openings (`osLevelOs`) from its call in numbers (`OsCall`).

**Off arrays, consecutive cells incrementally.** `vsPiOfA T rd σ Vn cl` reads the same proof off
the tables `T` (`WhirTabs`: the lanes of `g^k`, the stream words and the calls of each candidate),
built once by the caller (`whirTabs`), and reads consecutive cells by stepping the address by `g`
(`wordsFrom`: `readN`, `wordsAt`; `posOfW`: `posOf`), each query's position once (`oqQueryAt`),
each loop iteration's frame at `x·g^j` by stepping `x` (`oqItersFrom`), the loop's other
arguments once (`oqLoopArgs σ`, an argument), the selected candidate and its `open_stacked`
frame once (`vsPiOfM`, `vsPiOfAt`); `vsPiOfA_tabs`: at `whirTabs` it is `vsPiOfN`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The queries of `opening_queries`** from its frame `σ`, its loop the frames `loop` of `Vn`
(`oqsOf`). -/
def oqsOfN (s : Oq) (odd loop N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) : List QW :=
  (if odd = 1 then [oqQueryW s rd (σ (.n 12)) 13 true σ] else []) ++
    (List.range N).flatMap fun j ↦ oqIterOf s rd (Vn loop (gen ^ j :: oqLoopArgs σ) [])

/-- **A level's openings** from its `opening_queries` call `c`, the caller's frame `σ`
(`osLevelOs`). -/
def levelOsN (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) : List Opening :=
  let a := c.args.map fun k ↦ σ (.n k)
  (oqsOfN ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N rd (Vn c.fn a (c.rets.map fun k ↦ σ (.n k)))
    Vn).map (toOpening rd (a.headD 0) c.cd c.depth)

/-- **The child proof `verify_sub` checks** (`vsPiOf`), the frames numbered, `cl` the cursor's
length (`cursorLen`). -/
def vsPiOfN (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) : Proof :=
  let m := logGT (σ (.n 1901)) 28
  let fr := Vn (openStackedIdx m) (vsOsArgs σ) (vsOsRets σ)
  ⟨wordsAt rd (σ (.n 27)) (cl (σ (.n 27)) (σ (.n 868))) ++
      readN rd (fr (.n 8)) (osWordsTab.getD m 0),
    (osCallsTab.getD m []).flatMap (levelOsN rd fr Vn)⟩

/-! ## Equal to the original -/

/-- `open_stacked`'s specializations are the functions `openStackedIdx m`. -/
theorem openNames_eq :
    openNames = (List.range 28).map fun m ↦ decoderFunctionName (openStackedIdx m) := by
  simp only [openNames, ← natStr_eq]
  decide +kernel

theorem dispatchIdx_eq_logGT (x : E) : dispatchIdx x = logGT x 28 := by
  rw [← logG_eq_logGT _ (by norm_num)]
  unfold dispatchIdx logG
  congr 2

theorem map_vIdx {σ : Val} : ∀ {l : List V}, l.all isN = true →
    (l.map vIdx).map (fun k ↦ σ (.n k)) = l.map σ
  | [], _ => rfl
  | v :: l, h => by
      simp only [List.all_cons, Bool.and_eq_true, isN, beq_iff_eq] at h
      simp only [List.map_cons, vIdx, map_vIdx h.2, ← h.1]

theorem levelOsN_eq (rd : Reader) (σ : Val) (Fm : FrameMap) {r : OsCall}
    {c : ℕ × OsLv × String × List V × List V} (h : callMatch r c = true) :
    levelOsN rd σ (fun k ↦ Fm (decoderFunctionName k)) r = osLevelOs rd σ Fm c := by
  obtain ⟨lvl, lv, name, args, rets⟩ := c
  obtain ⟨base, I, pd, cd, odd, N, fn, loop, depth, rargs, rrets⟩ := r
  simp only [callMatch, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hI⟩, hpd⟩, hcd⟩, hodd⟩, hN⟩, hdep⟩, hra⟩, hrr⟩, ha⟩, hr⟩, hn⟩, hl⟩ := h
  subst hb hI hpd hcd hodd hN hdep hra hrr
  simp only [levelOsN, osLevelOs, lvOpenings, lvW, oqsOfN, oqsOf, map_vIdx ha, map_vIdx hr, hn, hl]
  rfl

theorem flatMap_zip {α β γ : Type} {g : α → List γ} {h : β → List γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ p ∈ l₁.zip l₂, g p.1 = h p.2) → l₁.flatMap g = l₂.flatMap h
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, hp => by
      simp only [List.flatMap_cons]
      rw [hp (a, b) (by simp), flatMap_zip (by simpa using hl)
        (fun p hm ↦ hp p (List.mem_cons_of_mem _ hm))]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem vsPiOfN_eq (rd : Reader) (σ : Val) (Fm : FrameMap) :
    vsPiOfN rd σ (fun k ↦ Fm (decoderFunctionName k)) cursorLen = vsPiOf rd σ Fm := by
  have hm := logG_lt (σ (.n 1901)) (bound := 28) (by norm_num)
  rw [logG_eq_logGT _ (by norm_num)] at hm
  have hname : decoderFunctionName (openStackedIdx (logGT (σ (.n 1901)) 28)) =
      openNames.getD (logGT (σ (.n 1901)) 28) "" := by
    rw [openNames_eq, getD_map_range hm]
  obtain ⟨hlen, hok⟩ := callsOK _ hm
  unfold vsPiOfN vsPiOf piOfW vsOsW open_stacked_osW
  simp only [dispatchIdx_eq_logGT, hname, osWordsTab_eq, getD_map_range hm]
  rw [Proof.mk.injEq]
  refine ⟨rfl, ?_⟩
  exact flatMap_zip hlen fun p hp ↦ levelOsN_eq rd _ Fm (List.all_eq_true.mp hok p hp)

/-! ## Consecutive cells, incrementally -/

/-- **The `n` words from the address `a` on**, each address the last's times `g` (`0` where the
memory has none). -/
def wordsFrom (rd : Reader) : K → ℕ → List E
  | _, 0 => []
  | a, n + 1 => (rd a).getD 0 :: wordsFrom rd (a * Parameters.g) n

theorem wordsFrom_gpow (rd : Reader) (a : K) : ∀ n k, wordsFrom rd (a * Parameters.gpow k) n =
    (List.range' k n).map fun i ↦ (rd (a * Parameters.gpow i)).getD 0
  | 0, _ => rfl
  | n + 1, k => by
    rw [wordsFrom, List.range'_succ, List.map_cons,
      show a * Parameters.gpow k * Parameters.g = a * Parameters.gpow (k + 1) by
        show a * Parameters.g ^ k * Parameters.g = a * Parameters.g ^ (k + 1)
        rw [pow_succ, mul_assoc],
      wordsFrom_gpow rd a n (k + 1)]

theorem wordsFrom_eq (rd : Reader) (a : K) (n : ℕ) :
    wordsFrom rd a n = (List.range n).map fun i ↦ (rd (a * Parameters.gpow i)).getD 0 := by
  have h := wordsFrom_gpow rd a n 0
  rw [show a * Parameters.gpow 0 = a by show a * Parameters.g ^ 0 = a; rw [pow_zero, mul_one]] at h
  rw [h, List.range_eq_range']

theorem readN_eq_wordsFrom (rd : Reader) (p : E) (n : ℕ) : readN rd p n = wordsFrom rd (p.limb 0) n := by
  rw [wordsFrom_eq]; rfl

theorem readN_eq_wordsAt (rd : Reader) (p : E) (n : ℕ) : readN rd p n = wordsAt rd p n := rfl

theorem wordsAt_eq_wordsFrom (rd : Reader) (p : E) (n : ℕ) :
    wordsAt rd p n = wordsFrom rd (p.limb 0) n := by
  rw [wordsFrom_eq]; rfl

/-- The number whose bits, low first, are the words equal to `1`. -/
def bitsW : List E → ℕ
  | [] => 0
  | w :: ws => (if w = 1 then 1 else 0) + 2 * bitsW ws

theorem bitsW_append (l : List E) (w : E) :
    bitsW (l ++ [w]) = bitsW l + 2 ^ l.length * (if w = 1 then 1 else 0) := by
  generalize hc : (if w = 1 then 1 else 0 : ℕ) = c
  induction l with
  | nil =>
    show (if w = 1 then 1 else 0) + 2 * 0 = 0 + 2 ^ 0 * c
    rw [hc]; omega
  | cons x l ih =>
    show (if x = 1 then 1 else 0) + 2 * bitsW (l ++ [w]) =
      ((if x = 1 then 1 else 0) + 2 * bitsW l) + 2 ^ (l.length + 1) * c
    rw [ih, pow_succ]
    ring

theorem bitsVal_eq_bitsW (h : ℕ → E) : ∀ n,
    LeanVM.Guest.Value.bitsVal (fun l ↦ decide (h l = 1)) n = bitsW ((List.range n).map h)
  | 0 => rfl
  | n + 1 => by
    rw [LeanVM.Guest.Value.bitsVal, bitsVal_eq_bitsW h n, List.range_succ, List.map_append,
      List.map_singleton, bitsW_append, List.length_map, List.length_range]
    by_cases hn : h n = 1
    · rw [decide_eq_true hn, ite_eq_left_iff.mpr (fun h ↦ absurd hn h)]; rfl
    · rw [decide_eq_false hn, ite_eq_right_iff.mpr (fun h ↦ absurd h hn)]; rfl

/-- **The position whose `D` bits the run at `bp` holds** (`posOf`), its cells read in a row. -/
def posOfW (rd : Reader) (bp : E) (D : ℕ) : ℕ := bitsW (wordsFrom rd (bp.limb 0) D)

theorem posOfW_eq (rd : Reader) (bp : E) (D : ℕ) : posOfW rd bp D = posOf rd bp D := by
  rw [posOfW, posOf, bitsVal_eq_bitsW, wordsFrom_eq]
  rfl

/-! ## The queries, each position once, the loop's frames stepped -/

/-- The query hinted at `b`, its position `pos` given (`oqQueryW`). -/
def oqQueryAt (s : Oq) (σ : Val) (b : ℕ) (emit : Bool) (pos : ℕ) : QW :=
  (pos, oqRow b s.R σ, oqSibsOf s.pd (oqCh s b emit) pos σ)

/-- **The query hinted at `b`**, its position read once (`oqQueryW`). -/
def oqQueryA (s : Oq) (rd : Reader) (bp : E) (b : ℕ) (emit : Bool) (σ : Val) : QW :=
  oqQueryAt s σ b emit (posOfW rd bp (s.pd + s.cd))

theorem oqQueryA_eq (s : Oq) (rd : Reader) (bp : E) (b : ℕ) (emit : Bool) (σ : Val) :
    oqQueryA s rd bp b emit σ = oqQueryW s rd bp b emit σ := by
  rw [oqQueryA, oqQueryAt, oqQueryW, posOfW_eq]

/-- A loop iteration's queries, from its frame (`oqIterOf`). -/
def oqIterA (s : Oq) (rd : Reader) (σ : Val) : List QW :=
  if s.base = 1 then
    [oqQueryA s rd (σ (.n 10)) 11 true σ, oqQueryA s rd (σ (.n (oqE1 s))) (oqE1 s + 1) false σ]
  else [oqQueryA s rd (σ (.n 9)) 10 true σ]

theorem oqIterA_eq (s : Oq) (rd : Reader) (σ : Val) : oqIterA s rd σ = oqIterOf s rd σ := by
  simp only [oqIterA, oqIterOf, oqQueryA_eq]

/-- **The loop's iterations from the frame at `x`**, `n` of them, the next at `x·g`: each the
queries of the frame of the loop's call `x :: la` (`la` the loop's other arguments). -/
def oqItersFrom (s : Oq) (loop : ℕ) (rd : Reader) (Vn : NFrames) (la : List E) :
    ℕ → E → List QW
  | 0, _ => []
  | n + 1, x => oqIterA s rd (Vn loop (x :: la) []) ++ oqItersFrom s loop rd Vn la n (x * gen)

theorem oqItersFrom_gen (s : Oq) (loop : ℕ) (rd : Reader) (Vn : NFrames) (la : List E) :
    ∀ n k, oqItersFrom s loop rd Vn la n (gen ^ k) =
      (List.range' k n).flatMap fun j ↦ oqIterOf s rd (Vn loop (gen ^ j :: la) [])
  | 0, _ => rfl
  | n + 1, k => by
    rw [oqItersFrom, ← pow_succ, oqItersFrom_gen s loop rd Vn la n (k + 1), List.range'_succ,
      List.flatMap_cons, oqIterA_eq]

/-- **`opening_queries`' queries** (`oqsOfN`): its loop's other arguments read once, each
iteration's frame at the next power of `g`, each query's position once. -/
def oqsOfA (s : Oq) (odd loop N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) : List QW :=
  (if odd = 1 then [oqQueryA s rd (σ (.n 12)) 13 true σ] else []) ++
    oqItersFrom s loop rd Vn (oqLoopArgs σ) N 1

theorem oqsOfA_eq (s : Oq) (odd loop N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    oqsOfA s odd loop N rd σ Vn = oqsOfN s odd loop N rd σ Vn := by
  have h := oqItersFrom_gen s loop rd Vn (oqLoopArgs σ) N 0
  rw [pow_zero] at h
  unfold oqsOfA oqsOfN
  rw [h, oqQueryA_eq, List.range_eq_range']

/-- A level's openings from its call `c`, the call's argument words `a` given (`levelOsN`). -/
def levelOsAt (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) (a : List E) : List Opening :=
  (oqsOfA ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N rd (Vn c.fn a (c.rets.map fun k ↦ σ (.n k)))
    Vn).map (toOpening rd (a.headD 0) c.cd c.depth)

/-- **A level's openings** (`levelOsN`), its call's argument words read once. -/
def levelOsA (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) : List Opening :=
  levelOsAt rd σ Vn c (c.args.map fun k ↦ σ (.n k))

theorem levelOsA_eq (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) :
    levelOsA rd σ Vn c = levelOsN rd σ Vn c := by
  rw [levelOsA, levelOsAt, levelOsN, oqsOfA_eq]

/-- `open_stacked`'s tables, as arrays: the lanes of `g^k` (`gLanes`), each candidate's stream
words (`osWordsTab`) and `opening_queries` calls (`osCallsTab`). -/
structure WhirTabs where
  lanes : List ℕ
  words : Array ℕ
  calls : Array (List OsCall)

/-- **`open_stacked`'s tables**, built from the literals. -/
def whirTabs : WhirTabs := ⟨gLanes, osWordsTab.toArray, osCallsTab.toArray⟩

/-- The child proof, its candidate `m` and the frame `fr` of its `open_stacked` call given
(`vsPiOfN`). -/
def vsPiOfAt (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (m : ℕ)
    (fr : Val) : Proof :=
  ⟨wordsFrom rd ((σ (.n 27)).limb 0) (cl (σ (.n 27)) (σ (.n 868))) ++
      wordsFrom rd ((fr (.n 8)).limb 0) (T.words.getD m 0),
    (T.calls.getD m []).flatMap (levelOsA rd fr Vn)⟩

/-- The child proof, its candidate `m` given: the frame of `open_stacked__L{m}`'s call read once. -/
def vsPiOfM (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (m : ℕ) :
    Proof :=
  vsPiOfAt T rd σ Vn cl m (Vn (openStackedIdx m) (vsOsArgs σ) (vsOsRets σ))

/-- **The child proof `verify_sub` checks, off the tables `T`** (`vsPiOfN`). -/
def vsPiOfA (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) : Proof :=
  vsPiOfM T rd σ Vn cl (logGTWith T.lanes (σ (.n 1901)) 28)

/-- **Off the tables built, the reader is `vsPiOfN`.** -/
theorem vsPiOfA_tabs (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) :
    vsPiOfA whirTabs rd σ Vn cl = vsPiOfN rd σ Vn cl := by
  have hl : levelOsA rd = levelOsN rd := funext fun σ ↦ funext fun Vn ↦ funext fun c ↦
    levelOsA_eq rd σ Vn c
  simp only [vsPiOfA, vsPiOfM, vsPiOfAt, vsPiOfN, whirTabs, logGTWith_gLanes, getD_toArray, hl,
    ← wordsAt_eq_wordsFrom, readN_eq_wordsAt]

end
end LeanVM.Guest.Fast
