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

end
end LeanVM.Guest.Fast
